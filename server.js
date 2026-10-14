'use strict';

/**
 * Виселица Онлайн — сервер.
 * Express раздаёт статику, Socket.IO синхронизирует игру в реальном времени.
 * Все комнаты и состояние игры живут только в оперативной памяти процесса.
 * Загаданное слово не покидает сервер, пока раунд не завершён.
 */

const path = require('path');
const http = require('http');
const crypto = require('crypto');
const express = require('express');
const { Server } = require('socket.io');
const WORDS = require('./words');

const PORT = Number(process.env.PORT) || 3000;
const MAX_WRONG = 6; // общее число ошибок до поражения
const POINTS_PER_LETTER = 10; // за каждое вхождение верной буквы
const SOLVE_BONUS = 20; // бонус тому, кто открыл последнюю букву
const GRACE_MS = Number(process.env.RECONNECT_GRACE_MS) || 60 * 1000; // время на возвращение
const IDLE_ROOM_MS = 30 * 60 * 1000; // чистка забытых комнат
const CPU_DELAY_MIN = Number(process.env.CPU_DELAY_MIN) || 1000;
const CPU_DELAY_MAX = Number(process.env.CPU_DELAY_MAX) || 2000;
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // без похожих символов (0/O, 1/I)
const CODE_LEN = 5;

const ALPHABETS = {
  ru: 'абвгдежзийклмнопрстуфхцчшщъыьэюя'.split(''),
  en: 'abcdefghijklmnopqrstuvwxyz'.split(''),
};
const FREQ_ORDER = {
  ru: 'оеаинтсрвлкмдпуяыьгзбчйхжшюцщэфъ'.split(''),
  en: 'etaoinshrdlcumwfgypbvkjxqz'.split(''),
};

const normalizeWord = (w) => w.toLowerCase().replace(/ё/g, 'е');

// Плоский пул слов: { word, category }
const POOL = {};
for (const lang of Object.keys(WORDS)) {
  const seen = new Set();
  POOL[lang] = [];
  for (const [category, list] of Object.entries(WORDS[lang])) {
    for (const raw of list) {
      const word = normalizeWord(raw);
      if (seen.has(word)) continue;
      seen.add(word);
      POOL[lang].push({ word, category });
    }
  }
}

/* ------------------------------------------------------------------ */
/* Приложение и сервер                                                 */
/* ------------------------------------------------------------------ */

const app = express();
app.disable('x-powered-by');
app.use(express.static(path.join(__dirname, 'public'), { maxAge: '5m' }));
app.get('/healthz', (req, res) => res.json({ ok: true, rooms: rooms.size, uptime: process.uptime() }));
app.get('/r/:code', (req, res) => res.redirect('/?room=' + encodeURIComponent(String(req.params.code).slice(0, 12))));

const server = http.createServer(app);
const io = new Server(server, {
  cors: process.env.CORS_ORIGIN ? { origin: process.env.CORS_ORIGIN.split(',').map((s) => s.trim()) } : undefined,
  pingInterval: 10000,
  pingTimeout: 8000,
  maxHttpBufferSize: 1e4,
});

/* ------------------------------------------------------------------ */
/* Хранилище в памяти                                                  */
/* ------------------------------------------------------------------ */

const rooms = new Map(); // code -> room
const queue = { ru: [], en: [] }; // очередь подбора соперника: { socket, name }

const now = () => Date.now();
const rndInt = (n) => crypto.randomInt(n);
const rndBetween = (a, b) => a + Math.floor(Math.random() * (b - a + 1));

function genCode() {
  for (;;) {
    let code = '';
    for (let i = 0; i < CODE_LEN; i++) code += CODE_CHARS[rndInt(CODE_CHARS.length)];
    if (!rooms.has(code)) return code;
  }
}

function sanitizeName(name) {
  const clean = String(name == null ? '' : name)
    .replace(/[\u0000-\u001f\u007f<>]/g, '')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 16);
  return clean || 'Player';
}

function pickLang(lang) {
  return lang === 'en' ? 'en' : 'ru';
}

function createRoom(mode, lang) {
  const room = {
    code: genCode(),
    mode, // 'online' | 'cpu'
    lang,
    phase: 'waiting', // 'waiting' | 'playing' | 'roundover'
    round: 0,
    players: [null, null],
    word: null,
    category: null,
    mask: [],
    used: [],
    wrong: 0,
    turn: 0,
    result: null,
    usedWords: new Set(),
    cpuTimer: null,
    lastActivity: now(),
    createdAt: now(),
  };
  rooms.set(room.code, room);
  return room;
}

function addPlayer(room, slot, name, socket, isCpu = false) {
  const player = {
    slot,
    token: crypto.randomBytes(16).toString('hex'),
    name,
    socketId: socket ? socket.id : null,
    status: 'online', // 'online' | 'connecting' | 'disconnected'
    score: 0,
    roundPoints: 0,
    wins: 0,
    isCpu,
    graceTimer: null,
    reconnectUntil: 0,
  };
  room.players[slot] = player;
  return player;
}

function attach(socket, room, player) {
  socket.data.code = room.code;
  socket.data.token = player.token;
  socket.join(room.code);
}

function detach(socket) {
  if (!socket) return;
  if (socket.data.code) socket.leave(socket.data.code);
  socket.data.code = null;
  socket.data.token = null;
}

function getCtx(socket) {
  const room = socket.data.code ? rooms.get(socket.data.code) : null;
  if (!room) return {};
  const player = room.players.find((p) => p && p.token === socket.data.token);
  if (!player || player.socketId !== socket.id) return { room };
  return { room, player };
}

const socketOf = (player) => (player && player.socketId ? io.sockets.sockets.get(player.socketId) : null);

function dequeue(socket) {
  for (const lang of Object.keys(queue)) {
    queue[lang] = queue[lang].filter((e) => e.socket.id !== socket.id);
  }
}

function resetMatch(room) {
  room.round = 0;
  room.usedWords.clear();
  for (const p of room.players) if (p) { p.score = 0; p.roundPoints = 0; p.wins = 0; }
}

function resetToWaiting(room) {
  clearTimeout(room.cpuTimer);
  room.phase = 'waiting';
  room.word = null;
  room.category = null;
  room.mask = [];
  room.used = [];
  room.wrong = 0;
  room.result = null;
  room.turn = 0;
  for (const p of room.players) if (p) p.roundPoints = 0;
}

/* ------------------------------------------------------------------ */
/* Представление состояния (без загаданного слова!)                    */
/* ------------------------------------------------------------------ */

function view(room, slot) {
  const t = now();
  return {
    code: room.code,
    mode: room.mode,
    lang: room.lang,
    phase: room.phase,
    round: room.round,
    maxWrong: MAX_WRONG,
    wrong: room.wrong,
    category: room.phase === 'waiting' ? null : room.category,
    mask: room.mask, // открытые буквы или null — слово скрыто
    used: room.used,
    turn: room.turn,
    you: slot,
    alphabet: ALPHABETS[room.lang],
    players: room.players.map((p, i) =>
      p
        ? {
            slot: i,
            name: p.name,
            status: p.isCpu ? 'online' : p.status,
            score: p.score,
            roundPoints: p.roundPoints,
            wins: p.wins,
            isCpu: p.isCpu,
            you: i === slot,
            reconnectIn: p.reconnectUntil ? Math.max(0, p.reconnectUntil - t) : 0,
          }
        : { slot: i, empty: true, status: 'connecting', score: 0, roundPoints: 0, wins: 0, you: false, reconnectIn: 0 }
    ),
    // слово раскрывается ТОЛЬКО после завершения раунда
    result: room.result ? { type: room.result.type, winner: room.result.winner, word: room.result.word } : null,
  };
}

function broadcast(room) {
  for (const p of room.players) {
    if (!p || p.isCpu || !p.socketId) continue;
    const s = socketOf(p);
    if (s) s.emit('state', view(room, p.slot));
  }
}

function notifyOthers(room, exceptSlot, type, name) {
  for (const p of room.players) {
    if (!p || p.isCpu || p.slot === exceptSlot) continue;
    const s = socketOf(p);
    if (s) s.emit('notice', { type, name });
  }
}

/* ------------------------------------------------------------------ */
/* Игровая логика                                                      */
/* ------------------------------------------------------------------ */

function startRound(room) {
  clearTimeout(room.cpuTimer);
  const pool = POOL[room.lang];
  let pick = pool[rndInt(pool.length)];
  for (let i = 0; i < 25 && room.usedWords.has(pick.word); i++) pick = pool[rndInt(pool.length)];
  room.usedWords.add(pick.word);
  if (room.usedWords.size > pool.length * 0.8) room.usedWords.clear();

  room.word = pick.word;
  room.category = pick.category;
  room.mask = new Array(pick.word.length).fill(null);
  room.used = [];
  room.wrong = 0;
  room.result = null;
  room.round += 1;
  room.phase = 'playing';
  room.turn = (room.round - 1) % 2; // первый ход чередуется по раундам
  for (const p of room.players) if (p) p.roundPoints = 0;
  room.lastActivity = now();
  scheduleCpu(room);
}

function endRound(room, type, winner) {
  clearTimeout(room.cpuTimer);
  room.phase = 'roundover';
  room.result = { type, winner, word: room.word };
  if (type === 'win' && room.players[winner]) room.players[winner].wins += 1;
}

function applyGuess(room, slot, letter) {
  const player = room.players[slot];
  const positions = [];
  for (let i = 0; i < room.word.length; i++) if (room.word[i] === letter) positions.push(i);
  const hit = positions.length > 0;
  room.used.push({ letter, hit, by: slot });
  room.lastActivity = now();

  if (hit) {
    for (const i of positions) room.mask[i] = letter;
    const pts = POINTS_PER_LETTER * positions.length;
    player.score += pts;
    player.roundPoints += pts;
  } else {
    room.wrong += 1;
  }

  const solved = room.mask.every(Boolean);
  if (solved) {
    player.score += SOLVE_BONUS;
    player.roundPoints += SOLVE_BONUS;
    const [a, b] = room.players;
    let winner = slot;
    if (a && b && a.roundPoints !== b.roundPoints) winner = a.roundPoints > b.roundPoints ? 0 : 1;
    endRound(room, 'win', winner);
  } else if (room.wrong >= MAX_WRONG) {
    endRound(room, 'lose', null);
  } else {
    room.turn = 1 - slot;
  }
  broadcast(room);
  scheduleCpu(room);
}

/* ---------------------------- Компьютер ---------------------------- */

function cpuPick(room) {
  const alphabet = ALPHABETS[room.lang];
  const usedSet = new Set(room.used.map((u) => u.letter));
  const free = alphabet.filter((l) => !usedSet.has(l));
  const good = new Set(room.used.filter((u) => u.hit).map((u) => u.letter));
  const bad = new Set(room.used.filter((u) => !u.hit).map((u) => u.letter));

  // Компьютер не знает слово: он фильтрует словарь по открытым буквам, как это сделал бы человек.
  const cands = POOL[room.lang].filter(({ word }) => {
    if (word.length !== room.mask.length) return false;
    for (let i = 0; i < word.length; i++) {
      const m = room.mask[i];
      if (m) { if (word[i] !== m) return false; }
      else if (good.has(word[i]) || bad.has(word[i])) return false;
    }
    return true;
  });

  const freq = new Map(free.map((l) => [l, 0]));
  for (const { word } of cands) for (const l of new Set(word)) if (freq.has(l)) freq.set(l, freq.get(l) + 1);
  let ranked = free.slice().sort((a, b) => freq.get(b) - freq.get(a));
  if (!cands.length) {
    const order = FREQ_ORDER[room.lang];
    ranked = free.slice().sort((a, b) => order.indexOf(a) - order.indexOf(b));
  }
  const r = Math.random();
  const idx = r < 0.62 ? 0 : r < 0.86 ? 1 : 2; // иногда ошибается — с ним можно выиграть
  return ranked[Math.min(idx, ranked.length - 1)];
}

function scheduleCpu(room) {
  clearTimeout(room.cpuTimer);
  if (room.mode !== 'cpu' || room.phase !== 'playing' || room.turn !== 1) return;
  const human = room.players[0];
  if (!human || human.status !== 'online') return; // пока игрок отключён, компьютер ждёт
  room.cpuTimer = setTimeout(() => {
    if (!rooms.has(room.code) || room.phase !== 'playing' || room.turn !== 1) return;
    const letter = cpuPick(room);
    if (letter) applyGuess(room, 1, letter);
  }, rndBetween(CPU_DELAY_MIN, CPU_DELAY_MAX));
}

/* ----------------------- Выход и отключения ------------------------ */

function destroyRoom(room) {
  clearTimeout(room.cpuTimer);
  for (const p of room.players) {
    if (!p) continue;
    clearTimeout(p.graceTimer);
    const s = socketOf(p);
    if (s) detach(s);
  }
  rooms.delete(room.code);
}

function removePlayer(room, slot, reason) {
  const p = room.players[slot];
  if (!p) return;
  clearTimeout(p.graceTimer);
  room.players[slot] = null;
  const s = socketOf(p);
  if (s) detach(s);

  const humans = room.players.filter((x) => x && !x.isCpu);
  if (room.mode === 'cpu' || humans.length === 0) {
    destroyRoom(room);
    return;
  }
  resetToWaiting(room);
  notifyOthers(room, slot, reason === 'timeout' ? 'timeout' : 'left', p.name);
  broadcast(room);
}

function leaveCurrent(socket) {
  dequeue(socket);
  const { room, player } = getCtx(socket);
  if (room && player) removePlayer(room, player.slot, 'left');
  else detach(socket);
}

function onDisconnect(socket) {
  dequeue(socket);
  const { room, player } = getCtx(socket);
  if (!room || !player) return;
  player.socketId = null;
  player.status = 'disconnected';
  player.reconnectUntil = now() + GRACE_MS;
  clearTimeout(room.cpuTimer);
  player.graceTimer = setTimeout(() => {
    if (room.players[player.slot] === player && player.status === 'disconnected') {
      removePlayer(room, player.slot, 'timeout');
    }
  }, GRACE_MS);
  if (room.mode === 'online') {
    notifyOthers(room, player.slot, 'disconnected', player.name);
    broadcast(room);
  }
}

/* ------------------------------------------------------------------ */
/* Socket.IO события                                                   */
/* ------------------------------------------------------------------ */

io.on('connection', (socket) => {
  socket.data = { code: null, token: null, hits: [] };

  const allow = () => {
    const t = now();
    const hits = socket.data.hits;
    while (hits.length && t - hits[0] > 5000) hits.shift();
    hits.push(t);
    return hits.length <= 40;
  };

  const on = (event, handler) =>
    socket.on(event, (...args) => {
      const ack = typeof args[args.length - 1] === 'function' ? args.pop() : () => {};
      const payload = args[0] && typeof args[0] === 'object' ? args[0] : {};
      if (!allow()) return ack({ ok: false, error: 'rate_limited' });
      try {
        handler(payload, ack);
      } catch (err) {
        console.error(`[${event}]`, err);
        ack({ ok: false, error: 'server_error' });
      }
    });

  // Создать комнату для игры с другом
  on('room:create', (p, ack) => {
    leaveCurrent(socket);
    const room = createRoom('online', pickLang(p.lang));
    const me = addPlayer(room, 0, sanitizeName(p.name), socket);
    attach(socket, room, me);
    broadcast(room);
    ack({ ok: true, code: room.code, token: me.token });
  });

  // Присоединиться по коду / ссылке
  on('room:join', (p, ack) => {
    const code = String(p.code || '').toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 12);
    if (!code) return ack({ ok: false, error: 'bad_code' });
    let room = rooms.get(code);
    if (!room || room.mode !== 'online') return ack({ ok: false, error: 'not_found' });

    // Уже сидим в этой комнате — просто подтверждаем
    const existing = getCtx(socket);
    if (existing.room === room && existing.player) {
      return ack({ ok: true, code, token: existing.player.token });
    }

    leaveCurrent(socket);
    room = rooms.get(code);
    if (!room) return ack({ ok: false, error: 'not_found' });
    const slot = room.players.findIndex((x) => !x);
    if (slot === -1) return ack({ ok: false, error: 'full' });

    if (room.round > 0) resetMatch(room); // новый соперник — новый матч
    const me = addPlayer(room, slot, sanitizeName(p.name), socket);
    attach(socket, room, me);
    notifyOthers(room, slot, 'joined', me.name);
    startRound(room);
    broadcast(room);
    ack({ ok: true, code, token: me.token });
  });

  // Вернуться в комнату после обрыва связи / перезагрузки страницы
  on('room:rejoin', (p, ack) => {
    const code = String(p.code || '').toUpperCase().slice(0, 12);
    const token = String(p.token || '');
    const room = rooms.get(code);
    const player = room && room.players.find((x) => x && !x.isCpu && x.token === token);
    if (!room || !player) return ack({ ok: false, error: 'not_found' });

    if (player.socketId && player.socketId !== socket.id) {
      const old = socketOf(player);
      if (old) {
        detach(old);
        old.emit('kicked');
      }
    }
    if (socket.data.code && socket.data.code !== room.code) leaveCurrent(socket);
    clearTimeout(player.graceTimer);
    player.socketId = socket.id;
    player.status = 'online';
    player.reconnectUntil = 0;
    attach(socket, room, player);
    if (room.mode === 'online') notifyOthers(room, player.slot, 'back', player.name);
    scheduleCpu(room);
    broadcast(room);
    ack({ ok: true, code: room.code, token: player.token });
  });

  // Игра против компьютера (всё равно проверяется сервером)
  on('cpu:start', (p, ack) => {
    leaveCurrent(socket);
    const lang = pickLang(p.lang);
    const room = createRoom('cpu', lang);
    const me = addPlayer(room, 0, sanitizeName(p.name), socket);
    addPlayer(room, 1, lang === 'en' ? 'Computer' : 'Компьютер', null, true);
    attach(socket, room, me);
    startRound(room);
    broadcast(room);
    ack({ ok: true, code: room.code, token: me.token });
  });

  // «Играть онлайн» — подбор случайного соперника
  on('match:find', (p, ack) => {
    leaveCurrent(socket);
    const lang = pickLang(p.lang);
    const name = sanitizeName(p.name);
    const waiting = queue[lang];
    let other = null;
    while (waiting.length) {
      const cand = waiting.shift();
      if (cand.socket.connected && cand.socket.id !== socket.id) { other = cand; break; }
    }
    if (!other) {
      waiting.push({ socket, name });
      return ack({ ok: true, searching: true });
    }
    const room = createRoom('online', lang);
    const p0 = addPlayer(room, 0, other.name, other.socket);
    const p1 = addPlayer(room, 1, name, socket);
    attach(other.socket, room, p0);
    attach(socket, room, p1);
    startRound(room);
    other.socket.emit('match:found', { code: room.code, token: p0.token });
    ack({ ok: true, found: true, code: room.code, token: p1.token });
    broadcast(room);
  });

  on('match:cancel', (p, ack) => {
    dequeue(socket);
    ack({ ok: true });
  });

  // Ход: выбор буквы. Сервер проверяет всё: очередь, фазу, допустимость буквы.
  on('game:guess', (p, ack) => {
    const { room, player } = getCtx(socket);
    if (!room || !player) return ack({ ok: false, error: 'not_found' });
    if (room.phase !== 'playing') return ack({ ok: false, error: 'not_playing' });
    if (room.turn !== player.slot) return ack({ ok: false, error: 'not_your_turn' });
    const other = room.players[1 - player.slot];
    if (!other) return ack({ ok: false, error: 'not_playing' });
    const letter = String(p.letter || '').toLowerCase().replace(/ё/g, 'е');
    if (letter.length !== 1 || !ALPHABETS[room.lang].includes(letter)) return ack({ ok: false, error: 'bad_letter' });
    if (room.used.some((u) => u.letter === letter)) return ack({ ok: false, error: 'already_used' });
    applyGuess(room, player.slot, letter);
    ack({ ok: true });
  });

  // Новая игра (следующий раунд)
  on('game:next', (p, ack) => {
    const { room, player } = getCtx(socket);
    if (!room || !player) return ack({ ok: false, error: 'not_found' });
    if (room.players.some((x) => !x)) return ack({ ok: false, error: 'not_playing' });
    const allowed = room.phase === 'roundover' || (room.mode === 'cpu' && room.phase === 'playing');
    if (!allowed) return ack({ ok: false, error: 'not_finished' });
    startRound(room);
    broadcast(room);
    ack({ ok: true });
  });

  on('room:leave', (p, ack) => {
    leaveCurrent(socket);
    ack({ ok: true });
  });

  socket.on('disconnect', () => onDisconnect(socket));
});

/* ------------------------------------------------------------------ */
/* Уборка и запуск                                                     */
/* ------------------------------------------------------------------ */

const sweeper = setInterval(() => {
  const t = now();
  for (const room of rooms.values()) {
    const anyOnline = room.players.some((p) => p && !p.isCpu && p.status === 'online');
    if (!anyOnline && t - room.lastActivity > 2 * GRACE_MS) destroyRoom(room);
    else if (t - room.lastActivity > IDLE_ROOM_MS && room.phase !== 'playing') destroyRoom(room);
  }
}, 60 * 1000);
sweeper.unref();

function start(port = PORT) {
  return new Promise((resolve) => {
    server.listen(port, () => {
      const addr = server.address();
      console.log(`Виселица Онлайн запущена: http://localhost:${addr.port}`);
      resolve(addr.port);
    });
  });
}

if (require.main === module) {
  start();
  const shutdown = () => {
    console.log('Останавливаемся…');
    io.close(() => process.exit(0));
    setTimeout(() => process.exit(0), 2000).unref();
  };
  process.on('SIGTERM', shutdown);
  process.on('SIGINT', shutdown);
}

module.exports = { server, io, rooms, start };
