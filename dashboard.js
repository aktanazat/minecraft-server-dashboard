const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const { spawn, execFileSync } = require('child_process');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const https = require('https');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

const SERVER_DIR = __dirname;
const PROPERTIES_FILE = path.join(SERVER_DIR, 'server.properties');
const WHITELIST_FILE = path.join(SERVER_DIR, 'whitelist.json');
const BANNED_FILE = path.join(SERVER_DIR, 'banned-players.json');
const OPS_FILE = path.join(SERVER_DIR, 'ops.json');
const USERCACHE_FILE = path.join(SERVER_DIR, 'usercache.json');
const SERVER_JAR = path.join(SERVER_DIR, 'server.jar');

app.use(express.json());

// --- State ---

let mcProcess = null;
let externalServerPid = null;
let serverRunning = false;
let startTime = null;
let onlinePlayers = new Set();
let logBuffer = [];
const MAX_LOG_LINES = 2000;
let playerCountHistory = [];
let memoryHistory = [];
let latestTickStats = { tps: null, mspt: null };
let worldSizeCache = { bytes: null, updatedAt: 0, calculating: false };
const livePlayerPositions = new Map();

// --- Helpers ---

function readJsonFile(filepath) {
  try {
    return JSON.parse(fs.readFileSync(filepath, 'utf8'));
  } catch {
    return [];
  }
}

function readUsercache() {
  const entries = readJsonFile(USERCACHE_FILE);
  if (!Array.isArray(entries)) return [];
  return entries;
}

function normalizePlayerName(name) {
  return String(name || '').trim();
}

function isValidPlayerName(name) {
  return /^[A-Za-z0-9_]{1,16}$/.test(name);
}

function parseProperties() {
  const content = fs.readFileSync(PROPERTIES_FILE, 'utf8');
  const props = {};
  for (const line of content.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) continue;
    const eq = trimmed.indexOf('=');
    if (eq === -1) continue;
    props[trimmed.slice(0, eq)] = trimmed.slice(eq + 1);
  }
  return props;
}

function writeProperties(props) {
  const lines = ['#Minecraft server properties'];
  lines.push('#' + new Date().toString());
  for (const [key, value] of Object.entries(props)) {
    lines.push(`${key}=${value}`);
  }
  fs.writeFileSync(PROPERTIES_FILE, lines.join('\n') + '\n');
}

function parsePlayerDataFromFile(filepath) {
  const raw = fs.readFileSync(filepath);
  let data;
  try {
    data = zlib.gunzipSync(raw);
  } catch {
    data = zlib.inflateSync(raw);
  }
  return parseNBT(data);
}

function loadPlayerDataByName(name) {
  const wanted = normalizePlayerName(name);
  const lc = wanted.toLowerCase();
  const entry = readUsercache().find((u) => String(u.name || '').toLowerCase() === lc);
  if (!entry || !entry.uuid) return null;
  const filepath = path.join(SERVER_DIR, 'world', 'playerdata', `${entry.uuid}.dat`);
  if (!fs.existsSync(filepath)) return null;
  try {
    const nbt = parsePlayerDataFromFile(filepath);
    return { uuid: entry.uuid, name: entry.name || wanted, nbt };
  } catch {
    return null;
  }
}

function buildPlayerDetail(name) {
  const loaded = loadPlayerDataByName(name);
  if (!loaded || !loaded.nbt) return null;
  const n = loaded.nbt;
  const pos = Array.isArray(n.Pos) ? n.Pos : [0, 0, 0];
  const inventory = Array.isArray(n.Inventory) ? n.Inventory : [];
  return {
    uuid: loaded.uuid,
    name: loaded.name,
    online: onlinePlayers.has(loaded.name),
    position: {
      x: Number(pos[0] || 0),
      y: Number(pos[1] || 0),
      z: Number(pos[2] || 0),
      dimension: String(n.Dimension || 'unknown'),
    },
    stats: {
      health: Number(n.Health || 0),
      food: Number(n.foodLevel ?? n.FoodLevel ?? 0),
      xpLevel: Number(n.XpLevel || 0),
      xpTotal: Number(n.XpTotal || 0),
      selectedSlot: Number(n.SelectedItemSlot ?? -1),
      gameType: Number(n.playerGameType ?? -1),
    },
    inventory: inventory.map((it) => ({
      id: String(it.id || 'minecraft:air'),
      count: Number(it.Count || 0),
      slot: Number(it.Slot ?? -1),
    })),
  };
}

function addLog(line) {
  logBuffer.push(line);
  if (logBuffer.length > MAX_LOG_LINES) {
    logBuffer = logBuffer.slice(-MAX_LOG_LINES);
  }
  io.emit('log', line);
}

function sendCommand(cmd) {
  if (mcProcess && mcProcess.stdin.writable) {
    mcProcess.stdin.write(cmd + '\n');
    return true;
  }
  return false;
}

function ensureCommandChannel(res) {
  refreshServerState();
  if (!serverRunning) {
    res.status(400).json({ error: 'Server is not running' });
    return false;
  }
  if (!mcProcess || !mcProcess.stdin.writable) {
    res.status(400).json({ error: 'Server is running externally; command channel unavailable. Start via dashboard to enable commands.' });
    return false;
  }
  return true;
}

function isPidRunning(pid) {
  if (!pid) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

function detectExternalServerPid() {
  const lockPath = path.join(SERVER_DIR, 'world', 'session.lock');
  if (!fs.existsSync(lockPath)) return null;

  try {
    const out = execFileSync('lsof', ['-t', lockPath], { encoding: 'utf8' }).trim();
    if (!out) return null;
    const pid = parseInt(out.split('\n')[0], 10);
    return Number.isFinite(pid) ? pid : null;
  } catch {
    return null;
  }
}

function refreshServerState() {
  if (mcProcess) {
    externalServerPid = null;
    serverRunning = true;
    return;
  }
  const pid = detectExternalServerPid();
  externalServerPid = pid;
  serverRunning = Boolean(pid);
}

function parsePlayers(line) {
  // [HH:MM:SS] [Server thread/INFO]: PlayerName joined the game
  const joinMatch = line.match(/\[Server thread\/INFO\]: (\S+) joined the game/);
  if (joinMatch) {
    onlinePlayers.add(joinMatch[1]);
    io.emit('players', { type: 'join', name: joinMatch[1], online: [...onlinePlayers] });
    return;
  }

  // [HH:MM:SS] [Server thread/INFO]: PlayerName left the game
  const leaveMatch = line.match(/\[Server thread\/INFO\]: (\S+) left the game/);
  if (leaveMatch) {
    onlinePlayers.delete(leaveMatch[1]);
    livePlayerPositions.delete(leaveMatch[1]);
    io.emit('players', { type: 'leave', name: leaveMatch[1], online: [...onlinePlayers] });
    return;
  }

  // Response to /list: "There are X of a max of Y players online: ..."
  const listMatch = line.match(/There are (\d+) of a max of (\d+) players online: (.*)/);
  if (listMatch) {
    const names = listMatch[3].trim();
    onlinePlayers = new Set(names ? names.split(', ').filter(Boolean) : []);
    io.emit('players', { type: 'list', online: [...onlinePlayers] });
  }

  const tickMatch = line.match(/TPS from last 1m, 5m, 15m:\s*([\d.]+),\s*([\d.]+),\s*([\d.]+).*?MSPT:\s*([\d.]+),\s*([\d.]+),\s*([\d.]+)/i);
  if (tickMatch) {
    latestTickStats = {
      tps: Number.parseFloat(tickMatch[1]),
      mspt: Number.parseFloat(tickMatch[4]),
    };
  }

  const posPatterns = [
    /\[Server thread\/INFO\]: (\S+) has the following entity data: \[\s*(-?\d+(?:\.\d+)?)d?,\s*(-?\d+(?:\.\d+)?)d?,\s*(-?\d+(?:\.\d+)?)d?\s*\]/,
    /\[Server thread\/INFO\]: The data of entity (\S+) is: \[\s*(-?\d+(?:\.\d+)?)d?,\s*(-?\d+(?:\.\d+)?)d?,\s*(-?\d+(?:\.\d+)?)d?\s*\]/,
  ];
  for (const pattern of posPatterns) {
    const m = line.match(pattern);
    if (!m) continue;
    const x = Number.parseFloat(m[2]);
    const y = Number.parseFloat(m[3]);
    const z = Number.parseFloat(m[4]);
    if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) continue;
    livePlayerPositions.set(m[1], { x, y, z, t: Date.now() });
    break;
  }
}

// --- Minecraft Process Management ---

function startMinecraft() {
  refreshServerState();
  if (serverRunning) return false;

  mcProcess = spawn('java', ['-Xms2G', '-Xmx4G', '-jar', 'server.jar', 'nogui'], {
    cwd: SERVER_DIR,
    stdio: ['pipe', 'pipe', 'pipe'],
  });

  serverRunning = true;
  startTime = Date.now();
  onlinePlayers.clear();
  addLog('[Dashboard] Starting Minecraft server...');

  mcProcess.stdout.on('data', (data) => {
    const lines = data.toString().split('\n').filter(Boolean);
    for (const line of lines) {
      addLog(line);
      parsePlayers(line);
    }
  });

  mcProcess.stderr.on('data', (data) => {
    const lines = data.toString().split('\n').filter(Boolean);
    for (const line of lines) {
      addLog('[STDERR] ' + line);
    }
  });

  mcProcess.on('close', (code) => {
    addLog(`[Dashboard] Server process exited with code ${code}`);
    mcProcess = null;
    serverRunning = false;
    startTime = null;
    onlinePlayers.clear();
    io.emit('status', getStatus());
  });

  return true;
}

function stopMinecraft() {
  return new Promise((resolve) => {
    refreshServerState();
    if (!serverRunning) return resolve(false);

    if (!mcProcess && externalServerPid) {
      addLog(`[Dashboard] Stopping detected server process (pid ${externalServerPid})...`);
      const pid = externalServerPid;
      try {
        process.kill(pid, 'SIGTERM');
      } catch {
        refreshServerState();
        return resolve(false);
      }

      const timeout = setTimeout(() => {
        if (isPidRunning(pid)) {
          try {
            process.kill(pid, 'SIGKILL');
          } catch {}
        }
      }, 10000);

      const waitForExit = setInterval(() => {
        if (!isPidRunning(pid)) {
          clearInterval(waitForExit);
          clearTimeout(timeout);
          clearTimeout(failSafe);
          refreshServerState();
          resolve(true);
        }
      }, 250);
      const failSafe = setTimeout(() => {
        clearInterval(waitForExit);
        refreshServerState();
        resolve(!isPidRunning(pid));
      }, 15000);
      return;
    }

    addLog('[Dashboard] Stopping server...');
    sendCommand('stop');

    const timeout = setTimeout(() => {
      if (mcProcess) {
        mcProcess.kill('SIGKILL');
      }
      resolve(true);
    }, 30000);

    mcProcess.on('close', () => {
      clearTimeout(timeout);
      resolve(true);
    });
  });
}

function getStatus() {
  refreshServerState();
  return {
    running: serverRunning,
    uptime: startTime ? Date.now() - startTime : 0,
    playerCount: onlinePlayers.size,
    players: [...onlinePlayers],
    maxPlayers: parseInt(parseProperties()['max-players'] || '20', 10),
    tps: latestTickStats.tps,
    mspt: latestTickStats.mspt,
  };
}

// --- Periodic tasks ---

setInterval(() => {
  refreshServerState();
  if (serverRunning) {
    sendCommand('list');
    if (mcProcess && mcProcess.stdin.writable) {
      for (const name of onlinePlayers) {
        sendCommand(`data get entity ${name} Pos`);
      }
    }
  }
  io.emit('status', getStatus());

  playerCountHistory.push({ time: Date.now(), count: onlinePlayers.size });
  if (playerCountHistory.length > 360) playerCountHistory = playerCountHistory.slice(-360);

  if (mcProcess && mcProcess.pid) {
    try {
      const mem = process.memoryUsage();
      memoryHistory.push({ time: Date.now(), rss: mem.rss });
      if (memoryHistory.length > 360) memoryHistory = memoryHistory.slice(-360);
    } catch {}
  }
}, 5000);

// --- REST API ---

app.get('/api/status', (req, res) => {
  res.json(getStatus());
});

app.post('/api/start', (req, res) => {
  refreshServerState();
  if (serverRunning) {
    return res.json({
      ok: false,
      error: externalServerPid
        ? `Already running (detected pid ${externalServerPid})`
        : 'Already running',
    });
  }
  res.json({ ok: startMinecraft() });
});

app.post('/api/stop', async (req, res) => {
  if (!serverRunning) return res.json({ ok: false, error: 'Not running' });
  await stopMinecraft();
  res.json({ ok: true });
});

app.post('/api/restart', async (req, res) => {
  if (serverRunning) await stopMinecraft();
  await new Promise((r) => setTimeout(r, 2000));
  startMinecraft();
  res.json({ ok: true });
});

app.get('/api/logs', (req, res) => {
  res.json(logBuffer);
});

app.get('/api/properties', (req, res) => {
  res.json(parseProperties());
});

app.post('/api/properties', (req, res) => {
  const current = parseProperties();
  const updates = req.body;
  for (const [key, value] of Object.entries(updates)) {
    current[key] = value;
  }
  writeProperties(current);
  res.json({ ok: true });
});

app.get('/api/players', (req, res) => {
  res.json({
    online: [...onlinePlayers],
    whitelist: readJsonFile(WHITELIST_FILE),
    banned: readJsonFile(BANNED_FILE),
    ops: readJsonFile(OPS_FILE),
  });
});

app.get('/api/player/:name', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  const detail = buildPlayerDetail(name);
  if (!detail) return res.status(404).json({ error: 'Player data not found' });
  res.json(detail);
});

app.post('/api/player/:name/xp', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  const amount = Math.max(0, parseInt(req.body.amount, 10) || 0);
  const unit = req.body.unit === 'points' ? 'points' : 'levels';
  const mode = req.body.mode === 'set' ? 'set' : 'add';
  if (!ensureCommandChannel(res)) return;
  sendCommand(`xp ${mode} ${name} ${amount} ${unit}`);
  res.json({ ok: true });
});

app.post('/api/player/:name/give', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  const item = String(req.body.item || '').trim();
  const count = Math.max(1, Math.min(64, parseInt(req.body.count, 10) || 1));
  if (!/^minecraft:[a-z0-9_]+$/.test(item)) return res.status(400).json({ error: 'Invalid item id' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(`give ${name} ${item} ${count}`);
  res.json({ ok: true });
});

app.post('/api/player/:name/health', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  if (!ensureCommandChannel(res)) return;
  const mode = String(req.body.mode || 'heal');
  const amount = Math.max(1, parseInt(req.body.amount, 10) || 4);
  if (mode === 'set') {
    const hp = Math.max(1, Math.min(40, amount));
    sendCommand(`data merge entity ${name} {Health:${hp.toFixed(1)}f}`);
  } else if (mode === 'damage') {
    sendCommand(`damage ${name} ${amount}`);
  } else {
    const amp = Math.max(0, Math.min(4, Math.floor(amount / 4)));
    sendCommand(`effect give ${name} instant_health 1 ${amp} true`);
  }
  res.json({ ok: true });
});

app.post('/api/player/:name/feed', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(`effect give ${name} saturation 1 10 true`);
  res.json({ ok: true });
});

app.post('/api/player/:name/inventory/request', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(`data get entity ${name} Inventory`);
  res.json({ ok: true });
});

app.post('/api/player/:name/inventory', (req, res) => {
  const name = normalizePlayerName(req.params.name);
  if (!isValidPlayerName(name)) return res.status(400).json({ error: 'Invalid player name' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(`data get entity ${name} Inventory`);
  res.json({ ok: true });
});

app.post('/api/whitelist', (req, res) => {
  const { name } = req.body;
  if (!name) return res.status(400).json({ error: 'Name required' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(`whitelist add ${name}`);
  res.json({ ok: true });
});

app.delete('/api/whitelist/:name', (req, res) => {
  if (!ensureCommandChannel(res)) return;
  sendCommand(`whitelist remove ${req.params.name}`);
  res.json({ ok: true });
});

app.post('/api/ban', (req, res) => {
  const { name, reason } = req.body;
  if (!name) return res.status(400).json({ error: 'Name required' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(reason ? `ban ${name} ${reason}` : `ban ${name}`);
  res.json({ ok: true });
});

app.delete('/api/ban/:name', (req, res) => {
  if (!ensureCommandChannel(res)) return;
  sendCommand(`pardon ${req.params.name}`);
  res.json({ ok: true });
});

app.post('/api/ops', (req, res) => {
  const { name } = req.body;
  if (!name) return res.status(400).json({ error: 'Name required' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(`op ${name}`);
  res.json({ ok: true });
});

app.delete('/api/ops/:name', (req, res) => {
  if (!ensureCommandChannel(res)) return;
  sendCommand(`deop ${req.params.name}`);
  res.json({ ok: true });
});

app.post('/api/kick', (req, res) => {
  const { name, reason } = req.body;
  if (!name) return res.status(400).json({ error: 'Name required' });
  if (!ensureCommandChannel(res)) return;
  sendCommand(reason ? `kick ${name} ${reason}` : `kick ${name}`);
  res.json({ ok: true });
});

app.get('/api/worlds', (req, res) => {
  const entries = fs.readdirSync(SERVER_DIR)
    .filter((f) => f.startsWith('world_backup_'))
    .map((name) => {
      const stat = fs.statSync(path.join(SERVER_DIR, name));
      return { name, created: stat.birthtime || stat.mtime };
    })
    .sort((a, b) => new Date(b.created) - new Date(a.created));
  res.json(entries);
});

app.delete('/api/world/backup/:name', (req, res) => {
  const backupName = req.params.name;
  if (!backupName.startsWith('world_backup_')) {
    return res.status(400).json({ error: 'Invalid backup name' });
  }
  const backupDir = path.join(SERVER_DIR, backupName);
  if (!fs.existsSync(backupDir)) {
    return res.status(404).json({ error: 'Backup not found' });
  }
  fs.rmSync(backupDir, { recursive: true, force: true });
  res.json({ ok: true });
});

function directorySizeBytes(dirPath) {
  if (!fs.existsSync(dirPath)) return 0;
  let total = 0;
  const stack = [dirPath];
  while (stack.length) {
    const current = stack.pop();
    let entries = [];
    try {
      entries = fs.readdirSync(current, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const entry of entries) {
      const full = path.join(current, entry.name);
      if (entry.isDirectory()) stack.push(full);
      else if (entry.isFile()) {
        try {
          total += fs.statSync(full).size;
        } catch {}
      }
    }
  }
  return total;
}

function refreshWorldSizeCache() {
  if (worldSizeCache.calculating) return;
  worldSizeCache.calculating = true;
  setImmediate(() => {
    try {
      const worldDir = path.join(SERVER_DIR, 'world');
      worldSizeCache.bytes = directorySizeBytes(worldDir);
      worldSizeCache.updatedAt = Date.now();
    } finally {
      worldSizeCache.calculating = false;
    }
  });
}

app.get('/api/world/info', (req, res) => {
  const worldDir = path.join(SERVER_DIR, 'world');
  const regionDir = path.join(worldDir, 'region');
  const backups = fs.readdirSync(SERVER_DIR).filter((f) => f.startsWith('world_backup_'));
  const props = parseProperties();
  const regionCount = fs.existsSync(regionDir)
    ? fs.readdirSync(regionDir).filter((f) => f.endsWith('.mca')).length
    : 0;
  res.json({
    levelName: props['level-name'] || 'world',
    levelSeed: props['level-seed'] || '',
    worldSizeBytes: worldSizeCache.bytes,
    worldSizePending: worldSizeCache.bytes === null || worldSizeCache.calculating,
    worldSizeUpdatedAt: worldSizeCache.updatedAt,
    regionCount,
    backupCount: backups.length,
    cachedTiles: mapTileCache.size,
  });
  if (worldSizeCache.bytes === null || Date.now() - worldSizeCache.updatedAt > 15000) {
    refreshWorldSizeCache();
  }
});

app.post('/api/world/new', async (req, res) => {
  const { seed } = req.body;
  const wasRunning = serverRunning;

  if (wasRunning) {
    addLog('[Dashboard] Stopping server for new world generation...');
    await stopMinecraft();
    await new Promise((r) => setTimeout(r, 3000));
  }

  const worldDir = path.join(SERVER_DIR, 'world');
  if (fs.existsSync(worldDir)) {
    const backupName = `world_backup_${Date.now()}`;
    const backupDir = path.join(SERVER_DIR, backupName);
    fs.renameSync(worldDir, backupDir);
    addLog(`[Dashboard] Backed up world to ${backupName}`);
  }

  // Also remove nether/end
  for (const dim of ['world_nether', 'world_the_end']) {
    const dimPath = path.join(SERVER_DIR, dim);
    if (fs.existsSync(dimPath)) {
      fs.renameSync(dimPath, path.join(SERVER_DIR, `${dim}_backup_${Date.now()}`));
    }
  }

  if (seed !== undefined && seed !== '') {
    const props = parseProperties();
    props['level-seed'] = seed;
    writeProperties(props);
    addLog(`[Dashboard] Set world seed to: ${seed}`);
  }

  if (wasRunning) {
    await new Promise((r) => setTimeout(r, 1000));
    startMinecraft();
  }

  res.json({ ok: true });
});

app.post('/api/world/restore/:name', async (req, res) => {
  const backupName = req.params.name;
  const backupDir = path.join(SERVER_DIR, backupName);
  if (!fs.existsSync(backupDir)) {
    return res.status(404).json({ error: 'Backup not found' });
  }
  if (!backupName.startsWith('world_backup_')) {
    return res.status(400).json({ error: 'Invalid backup name' });
  }

  const wasRunning = serverRunning;
  if (wasRunning) {
    addLog('[Dashboard] Stopping server for world restore...');
    await stopMinecraft();
    await new Promise((r) => setTimeout(r, 3000));
  }

  const worldDir = path.join(SERVER_DIR, 'world');
  if (fs.existsSync(worldDir)) {
    const archiveName = `world_backup_${Date.now()}`;
    fs.renameSync(worldDir, path.join(SERVER_DIR, archiveName));
    addLog(`[Dashboard] Archived current world as ${archiveName}`);
  }

  fs.renameSync(backupDir, worldDir);
  addLog(`[Dashboard] Restored world from ${backupName}`);

  if (wasRunning) {
    await new Promise((r) => setTimeout(r, 1000));
    startMinecraft();
  }

  res.json({ ok: true });
});

app.get('/api/performance', (req, res) => {
  res.json({ playerCountHistory, memoryHistory });
});

// --- NBT Parser ---

function parseNBT(buf) {
  let pos = 0;
  const ubyte = () => buf.readUInt8(pos++);
  const ushort = () => { const v = buf.readUInt16BE(pos); pos += 2; return v; };
  const int = () => { const v = buf.readInt32BE(pos); pos += 4; return v; };
  const long = () => { const v = buf.readBigInt64BE(pos); pos += 8; return v; };
  const float = () => { const v = buf.readFloatBE(pos); pos += 4; return v; };
  const dbl = () => { const v = buf.readDoubleBE(pos); pos += 8; return v; };
  const str = () => { const n = ushort(); const s = buf.toString('utf8', pos, pos + n); pos += n; return s; };

  function tag(type) {
    switch (type) {
      case 1: return buf.readInt8(pos++);
      case 2: { const v = buf.readInt16BE(pos); pos += 2; return v; }
      case 3: return int();
      case 4: return long();
      case 5: return float();
      case 6: return dbl();
      case 7: { const n = int(); const a = buf.slice(pos, pos + n); pos += n; return a; }
      case 8: return str();
      case 9: { const t = ubyte(); const n = int(); const a = []; for (let i = 0; i < n; i++) a.push(tag(t)); return a; }
      case 10: return compound();
      case 11: { const n = int(); const a = new Int32Array(n); for (let i = 0; i < n; i++) a[i] = int(); return a; }
      case 12: { const n = int(); const a = []; for (let i = 0; i < n; i++) a.push(long()); return a; }
      default: return null;
    }
  }

  function compound() {
    const obj = {};
    let t;
    while ((t = ubyte()) !== 0) {
      const name = str();
      obj[name] = tag(t);
    }
    return obj;
  }

  const rootType = ubyte();
  if (rootType !== 10) return null;
  str();
  return compound();
}

// --- Block Colors ---

const BLOCK_COLORS = {
  'minecraft:grass_block': [127, 178, 56], 'minecraft:short_grass': [127, 178, 56],
  'minecraft:tall_grass': [127, 178, 56], 'minecraft:fern': [106, 153, 43],
  'minecraft:dirt': [134, 96, 67], 'minecraft:coarse_dirt': [134, 96, 67],
  'minecraft:dirt_path': [148, 124, 68], 'minecraft:rooted_dirt': [134, 96, 67],
  'minecraft:mud': [93, 82, 72], 'minecraft:farmland': [130, 96, 50],
  'minecraft:stone': [125, 125, 125], 'minecraft:granite': [149, 103, 86],
  'minecraft:diorite': [188, 182, 182], 'minecraft:andesite': [136, 136, 136],
  'minecraft:deepslate': [80, 80, 82], 'minecraft:tuff': [93, 93, 82],
  'minecraft:calcite': [220, 215, 210], 'minecraft:bedrock': [50, 50, 50],
  'minecraft:sand': [219, 207, 163], 'minecraft:red_sand': [190, 102, 33],
  'minecraft:gravel': [136, 126, 126], 'minecraft:clay': [160, 166, 180],
  'minecraft:sandstone': [216, 199, 135], 'minecraft:red_sandstone': [181, 97, 31],
  'minecraft:water': [61, 87, 214], 'minecraft:lava': [207, 92, 15],
  'minecraft:ice': [158, 190, 252], 'minecraft:packed_ice': [141, 180, 250],
  'minecraft:blue_ice': [116, 167, 253], 'minecraft:frosted_ice': [148, 185, 251],
  'minecraft:snow': [249, 255, 254], 'minecraft:snow_block': [249, 255, 254],
  'minecraft:powder_snow': [230, 240, 240],
  'minecraft:oak_log': [109, 85, 50], 'minecraft:spruce_log': [58, 37, 16],
  'minecraft:birch_log': [216, 210, 196], 'minecraft:jungle_log': [85, 67, 25],
  'minecraft:acacia_log': [103, 96, 86], 'minecraft:dark_oak_log': [60, 46, 26],
  'minecraft:mangrove_log': [84, 56, 33], 'minecraft:cherry_log': [52, 28, 33],
  'minecraft:oak_leaves': [55, 114, 21], 'minecraft:spruce_leaves': [32, 72, 32],
  'minecraft:birch_leaves': [60, 110, 30], 'minecraft:jungle_leaves': [41, 115, 8],
  'minecraft:acacia_leaves': [45, 102, 8], 'minecraft:dark_oak_leaves': [29, 80, 5],
  'minecraft:mangrove_leaves': [49, 94, 10], 'minecraft:cherry_leaves': [215, 162, 184],
  'minecraft:azalea_leaves': [52, 105, 10], 'minecraft:flowering_azalea_leaves': [60, 110, 20],
  'minecraft:oak_planks': [162, 130, 78], 'minecraft:cobblestone': [122, 122, 122],
  'minecraft:mossy_cobblestone': [100, 120, 100], 'minecraft:obsidian': [20, 18, 30],
  'minecraft:netherrack': [100, 30, 30], 'minecraft:end_stone': [219, 219, 163],
  'minecraft:mycelium': [111, 99, 107], 'minecraft:podzol': [107, 76, 29],
  'minecraft:moss_block': [71, 110, 37], 'minecraft:terracotta': [152, 94, 67],
  'minecraft:white_terracotta': [210, 178, 161], 'minecraft:orange_terracotta': [162, 84, 38],
  'minecraft:yellow_terracotta': [186, 133, 35], 'minecraft:brown_terracotta': [77, 51, 36],
  'minecraft:red_terracotta': [143, 61, 47], 'minecraft:light_gray_terracotta': [147, 124, 113],
  'minecraft:cactus': [54, 90, 19], 'minecraft:melon': [111, 145, 28],
  'minecraft:pumpkin': [198, 118, 24], 'minecraft:lily_pad': [32, 128, 48],
  'minecraft:seagrass': [38, 88, 30], 'minecraft:tall_seagrass': [38, 88, 30],
  'minecraft:kelp': [50, 100, 40], 'minecraft:kelp_plant': [50, 100, 40],
  'minecraft:dead_bush': [107, 84, 40], 'minecraft:sugar_cane': [100, 160, 60],
  'minecraft:vine': [40, 114, 10], 'minecraft:bamboo': [90, 130, 20],
  'minecraft:stone_bricks': [122, 121, 122], 'minecraft:bricks': [150, 97, 83],
  'minecraft:prismarine': [99, 171, 158], 'minecraft:dark_prismarine': [51, 91, 75],
};

function isAir(name) {
  return !name || name === 'minecraft:air' || name === 'minecraft:cave_air' || name === 'minecraft:void_air';
}

function blockColor(name) {
  if (!name) return [0, 0, 0];
  if (BLOCK_COLORS[name]) return BLOCK_COLORS[name];
  if (name.includes('log') || name.includes('stem') || name.includes('wood')) return [109, 85, 50];
  if (name.includes('leaves')) return [55, 114, 21];
  if (name.includes('planks')) return [162, 130, 78];
  if (name.includes('stone') || name.includes('ore')) return [125, 125, 125];
  if (name.includes('sand')) return [219, 207, 163];
  if (name.includes('terracotta')) return [152, 94, 67];
  if (name.includes('water')) return [61, 87, 214];
  if (name.includes('concrete')) return [140, 140, 140];
  return [120, 120, 120];
}

// --- Region/Map Rendering ---

const mapTileCache = new Map();
let mapOverlayCache = {
  villages: [],
  structures: [],
  spawners: [],
  regionKey: '',
};
const itemIconCache = new Map();
const ITEM_TEXTURE_VERSION = '1.21.4';
const mapGenerateState = {
  running: false,
  total: 0,
  done: 0,
  startedAt: 0,
  finishedAt: 0,
  error: '',
};

function renderRegionTile(filepath) {
  const buf = fs.readFileSync(filepath);
  const rgb = new Uint8Array(512 * 512 * 3);
  const heights = new Int32Array(512 * 512);

  for (let cz = 0; cz < 32; cz++) {
    for (let cx = 0; cx < 32; cx++) {
      const hi = (cx + cz * 32) * 4;
      const offset = ((buf[hi] << 16) | (buf[hi + 1] << 8) | buf[hi + 2]) * 4096;
      if (offset < 8192 || buf[hi + 3] === 0) continue;

      try {
        const length = buf.readUInt32BE(offset);
        const compression = buf[offset + 4];
        const compressed = buf.slice(offset + 5, offset + 4 + length);
        let data;
        if (compression === 2) data = zlib.inflateSync(compressed);
        else if (compression === 1) data = zlib.gunzipSync(compressed);
        else continue;

        const nbt = parseNBT(data);
        if (!nbt || !nbt.sections) continue;

        const topBlocks = new Array(256).fill(null);
        const topH = new Int32Array(256);
        let found = 0;

        const sections = [...nbt.sections]
          .filter(s => s && s.block_states)
          .sort((a, b) => Number(b.Y || 0) - Number(a.Y || 0));

        for (const section of sections) {
          if (found >= 256) break;
          const palette = section.block_states.palette;
          if (!palette || palette.length === 0) continue;
          const sY = Number(section.Y || 0) * 16;

          if (palette.length === 1) {
            if (isAir(palette[0].Name)) continue;
            for (let i = 0; i < 256; i++) {
              if (topBlocks[i] === null) {
                topBlocks[i] = palette[0].Name;
                topH[i] = sY + 15;
                found++;
              }
            }
            continue;
          }

          const sData = section.block_states.data;
          if (!sData || sData.length === 0) continue;
          const bpe = Math.max(4, Math.ceil(Math.log2(palette.length)));
          const epl = Math.floor(64 / bpe);
          const mask = (1n << BigInt(bpe)) - 1n;

          for (let y = 15; y >= 0 && found < 256; y--) {
            for (let z = 0; z < 16; z++) {
              for (let x = 0; x < 16; x++) {
                const ci = z * 16 + x;
                if (topBlocks[ci] !== null) continue;
                const bi = y * 256 + z * 16 + x;
                const li = Math.floor(bi / epl);
                const si = (bi % epl) * bpe;
                if (li >= sData.length) continue;
                const pi = Number((sData[li] >> BigInt(si)) & mask);
                if (pi >= palette.length) continue;
                const name = palette[pi].Name;
                if (isAir(name)) continue;
                topBlocks[ci] = name;
                topH[ci] = sY + y;
                found++;
              }
            }
          }
        }

        for (let bz = 0; bz < 16; bz++) {
          for (let bx = 0; bx < 16; bx++) {
            const px = cx * 16 + bx;
            const pz = cz * 16 + bz;
            const ri = pz * 512 + px;
            const ci = bz * 16 + bx;
            const [r, g, b] = blockColor(topBlocks[ci]);
            rgb[ri * 3] = r;
            rgb[ri * 3 + 1] = g;
            rgb[ri * 3 + 2] = b;
            heights[ri] = topH[ci];
          }
        }
      } catch {}
    }
  }

  // Hillshade
  for (let z = 0; z < 512; z++) {
    for (let x = 0; x < 512; x++) {
      const i = z * 512 + x;
      if (heights[i] === 0 && rgb[i * 3] === 0) continue;
      const h = heights[i];
      const hL = x > 0 ? heights[i - 1] : h;
      const hU = z > 0 ? heights[i - 512] : h;
      const shade = Math.max(-25, Math.min(25, ((h - hL) + (h - hU)) * 4));
      for (let c = 0; c < 3; c++) {
        rgb[i * 3 + c] = Math.max(0, Math.min(255, rgb[i * 3 + c] + shade));
      }
    }
  }

  return rgb;
}

function toSeedInt(seedValue) {
  const s = String(seedValue ?? '');
  let h = 2166136261 >>> 0;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  return h >>> 0;
}

function hash2D(ix, iz, seed) {
  let h = seed >>> 0;
  h ^= Math.imul(ix, 374761393);
  h ^= Math.imul(iz, 668265263);
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
}

function smoothstep(t) {
  return t * t * (3 - 2 * t);
}

function lerp(a, b, t) {
  return a + (b - a) * t;
}

function valueNoise2D(x, z, seed) {
  const ix = Math.floor(x);
  const iz = Math.floor(z);
  const fx = x - ix;
  const fz = z - iz;
  const tx = smoothstep(fx);
  const tz = smoothstep(fz);
  const n00 = hash2D(ix, iz, seed);
  const n10 = hash2D(ix + 1, iz, seed);
  const n01 = hash2D(ix, iz + 1, seed);
  const n11 = hash2D(ix + 1, iz + 1, seed);
  const nx0 = lerp(n00, n10, tx);
  const nx1 = lerp(n01, n11, tx);
  return lerp(nx0, nx1, tz);
}

function fbm2D(x, z, seed, octaves) {
  let value = 0;
  let amp = 0.5;
  let freq = 1;
  let sum = 0;
  for (let i = 0; i < octaves; i++) {
    value += valueNoise2D(x * freq, z * freq, seed + i * 1013) * amp;
    sum += amp;
    amp *= 0.5;
    freq *= 2;
  }
  return sum > 0 ? value / sum : 0;
}

function seedPreviewColor(wx, wz, seedInt) {
  const elev = fbm2D(wx / 650, wz / 650, seedInt + 17, 5);
  const temp = fbm2D(wx / 900, wz / 900, seedInt + 73, 4);
  const wet = fbm2D(wx / 900, wz / 900, seedInt + 191, 4);
  const ridge = fbm2D(wx / 220, wz / 220, seedInt + 991, 3);
  const e = elev * 0.85 + ridge * 0.15;

  if (e < 0.32) return [54, 92, 190];
  if (e < 0.36) return [206, 195, 133];
  if (e > 0.82) return [245, 246, 248];
  if (e > 0.72) return [136, 136, 136];

  if (temp > 0.62 && wet < 0.38) return [192, 181, 112];
  if (wet > 0.66 && temp > 0.45) return [44, 118, 44];
  if (wet > 0.56) return [86, 142, 72];
  if (temp < 0.32) return [105, 132, 92];
  return [118, 152, 88];
}

function renderSeedPreviewTile(seedValue, rx, rz) {
  const seedInt = toSeedInt(seedValue);
  const rgb = new Uint8Array(512 * 512 * 3);
  const step = 4;
  const sampleSize = 512 / step;
  const sampled = new Uint8Array(sampleSize * sampleSize * 3);

  for (let sz = 0; sz < sampleSize; sz++) {
    for (let sx = 0; sx < sampleSize; sx++) {
      const wx = rx * 512 + sx * step;
      const wz = rz * 512 + sz * step;
      const [r, g, b] = seedPreviewColor(wx, wz, seedInt);
      const si = (sz * sampleSize + sx) * 3;
      sampled[si] = r;
      sampled[si + 1] = g;
      sampled[si + 2] = b;
    }
  }

  for (let z = 0; z < 512; z++) {
    const sz = Math.min(sampleSize - 1, Math.floor(z / step));
    for (let x = 0; x < 512; x++) {
      const sx = Math.min(sampleSize - 1, Math.floor(x / step));
      const si = (sz * sampleSize + sx) * 3;
      const i = (z * 512 + x) * 3;
      rgb[i] = sampled[si];
      rgb[i + 1] = sampled[si + 1];
      rgb[i + 2] = sampled[si + 2];
    }
  }
  return rgb;
}

function readPlayerMarkers() {
  const playerDir = path.join(SERVER_DIR, 'world', 'playerdata');
  if (!fs.existsSync(playerDir)) return [];

  const uuidToName = new Map(readJsonFile(USERCACHE_FILE).map((u) => [String(u.uuid || '').toLowerCase(), u.name]));
  const players = [];
  const files = fs.readdirSync(playerDir).filter((f) => f.endsWith('.dat'));

  for (const filename of files) {
    try {
      const uuid = filename.slice(0, -4).toLowerCase();
      const raw = fs.readFileSync(path.join(playerDir, filename));
      let data;
      try {
        data = zlib.gunzipSync(raw);
      } catch {
        data = zlib.inflateSync(raw);
      }
      const nbt = parseNBT(data);
      if (!nbt || !Array.isArray(nbt.Pos) || nbt.Pos.length < 3) continue;
      const x = Number(nbt.Pos[0]);
      const z = Number(nbt.Pos[2]);
      if (!Number.isFinite(x) || !Number.isFinite(z)) continue;
      const y = Number(nbt.Pos[1]);
      const name = uuidToName.get(uuid) || uuid;
      const live = livePlayerPositions.get(name);
      const useLive = Boolean(live && Date.now() - live.t < 30000);
      players.push({
        uuid,
        name,
        x: useLive ? live.x : x,
        y: useLive ? live.y : (Number.isFinite(y) ? y : 0),
        z: useLive ? live.z : z,
        online: onlinePlayers.has(name),
      });
    } catch {}
  }

  return players;
}

function getStructureStarts(nbt) {
  if (!nbt || typeof nbt !== 'object') return null;
  const candidates = [
    nbt.structures?.starts,
    nbt.structures?.Starts,
    nbt.Structures?.starts,
    nbt.Structures?.Starts,
  ];
  for (const starts of candidates) {
    if (starts && typeof starts === 'object' && !Array.isArray(starts)) return starts;
  }
  return null;
}

function getBlockEntities(nbt) {
  if (!nbt || typeof nbt !== 'object') return [];
  const candidates = [
    nbt.block_entities,
    nbt.blockEntities,
    nbt.BlockEntities,
    nbt.TileEntities,
  ];
  for (const c of candidates) {
    if (Array.isArray(c)) return c;
  }
  return [];
}

function structureTypeFromTokens(key, value) {
  const raw = String(value?.id || value?.Id || key || '').toLowerCase();
  const rules = [
    { type: 'ancient_city', label: 'Ancient City', test: ['ancient_city'] },
    { type: 'mansion', label: 'Mansion', test: ['mansion', 'woodland_mansion'] },
    { type: 'village', label: 'Village', test: ['village'] },
    { type: 'stronghold', label: 'Stronghold', test: ['stronghold'] },
    { type: 'trial_chambers', label: 'Trial Chambers', test: ['trial_chambers'] },
    { type: 'monument', label: 'Ocean Monument', test: ['monument'] },
    { type: 'outpost', label: 'Pillager Outpost', test: ['outpost'] },
    { type: 'shipwreck', label: 'Shipwreck', test: ['shipwreck'] },
    { type: 'ruined_portal', label: 'Ruined Portal', test: ['ruined_portal'] },
    { type: 'fortress', label: 'Nether Fortress', test: ['fortress'] },
    { type: 'bastion', label: 'Bastion', test: ['bastion'] },
    { type: 'end_city', label: 'End City', test: ['end_city'] },
    { type: 'mineshaft', label: 'Mineshaft', test: ['mineshaft'] },
    { type: 'temple', label: 'Temple', test: ['temple', 'pyramid', 'igloo', 'jungle'] },
  ];
  for (const r of rules) {
    if (r.test.some((t) => raw.includes(t))) return r;
  }
  return null;
}

function getChunkCoord(nbt, start, axis) {
  const chunkKeys = axis === 'x'
    ? [start?.ChunkX, start?.chunkX, nbt.xPos, nbt.ChunkX, nbt.chunk_x_pos]
    : [start?.ChunkZ, start?.chunkZ, nbt.zPos, nbt.ChunkZ, nbt.chunk_z_pos];
  for (const v of chunkKeys) {
    const n = Number(v);
    if (Number.isFinite(n)) return n;
  }
  return null;
}

function readMapFeatureMarkers() {
  const regionDir = path.join(SERVER_DIR, 'world', 'region');
  if (!fs.existsSync(regionDir)) {
    return { villages: [], structures: [], spawners: [] };
  }

  const regionFiles = fs.readdirSync(regionDir).filter((f) => f.endsWith('.mca')).sort();
  const regionKey = regionFiles.map((f) => `${f}:${fs.statSync(path.join(regionDir, f)).mtimeMs}`).join('|');
  if (mapOverlayCache.regionKey === regionKey) {
    return {
      villages: mapOverlayCache.villages,
      structures: mapOverlayCache.structures,
      spawners: mapOverlayCache.spawners,
    };
  }

  const structures = [];
  const villages = [];
  const spawners = [];
  const seenStructures = new Set();
  const seenSpawners = new Set();

  for (const file of regionFiles) {
    const filepath = path.join(regionDir, file);
    let buf;
    try {
      buf = fs.readFileSync(filepath);
    } catch {
      continue;
    }

    for (let cz = 0; cz < 32; cz++) {
      for (let cx = 0; cx < 32; cx++) {
        const hi = (cx + cz * 32) * 4;
        const offset = ((buf[hi] << 16) | (buf[hi + 1] << 8) | buf[hi + 2]) * 4096;
        if (offset < 8192 || buf[hi + 3] === 0) continue;

        try {
          const length = buf.readUInt32BE(offset);
          const compression = buf[offset + 4];
          const compressed = buf.slice(offset + 5, offset + 4 + length);
          let data;
          if (compression === 2) data = zlib.inflateSync(compressed);
          else if (compression === 1) data = zlib.gunzipSync(compressed);
          else continue;

          const nbt = parseNBT(data);
          const starts = getStructureStarts(nbt);
          if (starts) {
            for (const [key, value] of Object.entries(starts)) {
              const st = structureTypeFromTokens(key, value);
              if (!st) continue;
              const chunkX = getChunkCoord(nbt, value, 'x');
              const chunkZ = getChunkCoord(nbt, value, 'z');
              if (chunkX === null || chunkZ === null) continue;
              const markerKey = `${st.type}:${chunkX},${chunkZ}`;
              if (seenStructures.has(markerKey)) continue;
              seenStructures.add(markerKey);
              const marker = {
                type: st.type,
                label: st.label,
                x: chunkX * 16 + 8,
                z: chunkZ * 16 + 8,
              };
              structures.push(marker);
              if (st.type === 'village') villages.push(marker);
            }
          }

          const blockEntities = getBlockEntities(nbt);
          for (const be of blockEntities) {
            const id = String(be?.id || be?.Id || '').toLowerCase();
            if (!id.includes('spawner')) continue;
            const bx = Number(be?.x);
            const bz = Number(be?.z);
            if (!Number.isFinite(bx) || !Number.isFinite(bz)) continue;
            const sk = `${Math.round(bx)},${Math.round(bz)}`;
            if (seenSpawners.has(sk)) continue;
            seenSpawners.add(sk);
            spawners.push({ x: bx, z: bz, label: 'Dungeon/Spawner' });
          }
        } catch {}
      }
    }
  }

  mapOverlayCache = { villages, structures, spawners, regionKey };
  return { villages, structures, spawners };
}

function parseCompressedNbtFile(filepath) {
  if (!fs.existsSync(filepath)) return null;
  try {
    const raw = fs.readFileSync(filepath);
    let data;
    try {
      data = zlib.gunzipSync(raw);
    } catch {
      data = zlib.inflateSync(raw);
    }
    return parseNBT(data);
  } catch {
    return null;
  }
}

function readWorldSpawnMarker() {
  const nbt = parseCompressedNbtFile(path.join(SERVER_DIR, 'world', 'level.dat'));
  const data = nbt?.Data || nbt || null;
  if (!data) return null;
  const x = Number(data.SpawnX);
  const z = Number(data.SpawnZ);
  if (!Number.isFinite(x) || !Number.isFinite(z)) return null;
  return {
    x,
    z,
    y: Number.isFinite(Number(data.SpawnY)) ? Number(data.SpawnY) : 64,
    label: 'World Spawn',
  };
}

function readPlayerRespawnMarkers() {
  const playerDir = path.join(SERVER_DIR, 'world', 'playerdata');
  if (!fs.existsSync(playerDir)) return [];
  const uuidToName = new Map(readUsercache().map((u) => [String(u.uuid || '').toLowerCase(), u.name]));
  const markers = [];
  for (const filename of fs.readdirSync(playerDir).filter((f) => f.endsWith('.dat'))) {
    try {
      const uuid = filename.slice(0, -4).toLowerCase();
      const nbt = parseCompressedNbtFile(path.join(playerDir, filename));
      if (!nbt) continue;
      const x = Number(nbt.SpawnX);
      const z = Number(nbt.SpawnZ);
      if (!Number.isFinite(x) || !Number.isFinite(z)) continue;
      markers.push({
        name: uuidToName.get(uuid) || uuid,
        x,
        z,
        dimension: String(nbt.SpawnDimension || ''),
        label: 'Respawn',
      });
    } catch {}
  }
  return markers;
}

app.get('/api/map/regions', (req, res) => {
  const regionDir = path.join(SERVER_DIR, 'world', 'region');
  if (!fs.existsSync(regionDir)) return res.json([]);
  const files = fs.readdirSync(regionDir).filter(f => f.endsWith('.mca'));
  res.json(files.map(f => {
    const m = f.match(/r\.(-?\d+)\.(-?\d+)\.mca/);
    return m ? { x: parseInt(m[1]), z: parseInt(m[2]) } : null;
  }).filter(Boolean));
});

app.get('/api/map/tile/:rx/:rz', (req, res) => {
  const rx = parseInt(req.params.rx);
  const rz = parseInt(req.params.rz);
  const key = `${rx},${rz}`;
  if (mapTileCache.has(key)) {
    res.set('Content-Type', 'application/octet-stream');
    return res.send(Buffer.from(mapTileCache.get(key)));
  }
  const filepath = path.join(SERVER_DIR, 'world', 'region', `r.${rx}.${rz}.mca`);
  if (!fs.existsSync(filepath)) return res.status(404).send('Not found');
  const rgb = renderRegionTile(filepath);
  mapTileCache.set(key, rgb);
  res.set('Content-Type', 'application/octet-stream');
  res.send(Buffer.from(rgb));
});

app.get('/api/map/seed-tile/:rx/:rz', (req, res) => {
  const rx = parseInt(req.params.rx, 10);
  const rz = parseInt(req.params.rz, 10);
  const props = parseProperties();
  const seed = String(props['level-seed'] || '0');
  const key = `seed:${seed}:${rx},${rz}`;
  if (mapTileCache.has(key)) {
    res.set('Content-Type', 'application/octet-stream');
    return res.send(Buffer.from(mapTileCache.get(key)));
  }
  const rgb = renderSeedPreviewTile(seed, rx, rz);
  mapTileCache.set(key, rgb);
  res.set('Content-Type', 'application/octet-stream');
  res.send(Buffer.from(rgb));
});

app.post('/api/map/clear-cache', (req, res) => {
  mapTileCache.clear();
  mapOverlayCache = { villages: [], structures: [], spawners: [], regionKey: '' };
  res.json({ ok: true });
});

function startMapGenerateAll() {
  if (mapGenerateState.running) return false;
  const regionDir = path.join(SERVER_DIR, 'world', 'region');
  if (!fs.existsSync(regionDir)) {
    mapGenerateState.running = false;
    mapGenerateState.total = 0;
    mapGenerateState.done = 0;
    mapGenerateState.error = 'No world/region directory found';
    mapGenerateState.finishedAt = Date.now();
    return true;
  }

  const files = fs.readdirSync(regionDir).filter((f) => f.endsWith('.mca'));
  mapGenerateState.running = true;
  mapGenerateState.total = files.length;
  mapGenerateState.done = 0;
  mapGenerateState.startedAt = Date.now();
  mapGenerateState.finishedAt = 0;
  mapGenerateState.error = '';

  (async () => {
    try {
      for (const file of files) {
        const m = file.match(/r\.(-?\d+)\.(-?\d+)\.mca/);
        if (!m) {
          mapGenerateState.done += 1;
          continue;
        }
        const rx = parseInt(m[1], 10);
        const rz = parseInt(m[2], 10);
        const key = `${rx},${rz}`;
        const filepath = path.join(regionDir, file);
        const rgb = renderRegionTile(filepath);
        mapTileCache.set(key, rgb);
        mapGenerateState.done += 1;
        await new Promise((r) => setImmediate(r));
      }
    } catch (err) {
      mapGenerateState.error = err && err.message ? err.message : String(err);
    } finally {
      mapGenerateState.running = false;
      mapGenerateState.finishedAt = Date.now();
    }
  })();
  return true;
}

app.post('/api/map/generate-all', (req, res) => {
  const ok = startMapGenerateAll();
  if (!ok) return res.json({ ok: false, error: 'Generation already running' });
  res.json({ ok: true, status: mapGenerateState });
});

app.get('/api/map/generate-status', (req, res) => {
  res.json(mapGenerateState);
});

app.get('/api/map/overlays', (req, res) => {
  const f = readMapFeatureMarkers();
  res.json({
    players: readPlayerMarkers(),
    villages: f.villages,
    structures: f.structures,
    spawners: f.spawners,
    spawn: readWorldSpawnMarker(),
    respawns: readPlayerRespawnMarkers(),
  });
});

function readJarEntryBuffer(entryPath) {
  try {
    return execFileSync('unzip', ['-p', SERVER_JAR, entryPath], {
      encoding: 'buffer',
      maxBuffer: 2 * 1024 * 1024,
      stdio: ['ignore', 'pipe', 'ignore'],
    });
  } catch {
    return null;
  }
}

function readJarEntryText(entryPath) {
  const b = readJarEntryBuffer(entryPath);
  if (!b || b.length === 0) return null;
  try {
    return b.toString('utf8');
  } catch {
    return null;
  }
}

const ITEM_ICON_ALIASES = {
  hay: ['hay_block', 'hay_block_side', 'wheat'],
  white_bed: ['white_bed', 'red_bed', 'bed', 'white_wool'],
  shield: ['shield', 'shield_base', 'oak_planks', 'iron_ingot'],
  furnace: ['furnace_front', 'furnace_side', 'cobblestone'],
  sugar_cane: ['sugar_cane'],
};

const ITEM_ICON_TEXTURE_OVERRIDES = {
  white_bed: [
    'assets/minecraft/textures/item/white_bed.png',
    'assets/minecraft/textures/item/red_bed.png',
    'assets/minecraft/textures/entity/bed/white.png',
  ],
  shield: [
    'assets/minecraft/textures/item/shield.png',
    'assets/minecraft/textures/entity/shield/base_nopattern.png',
    'assets/minecraft/textures/entity/shield/base.png',
  ],
  hay: [
    'assets/minecraft/textures/block/hay_block_side.png',
  ],
  furnace: [
    'assets/minecraft/textures/block/furnace_front.png',
    'assets/minecraft/textures/block/furnace_side.png',
  ],
};

function normalizeTextureRef(ref) {
  if (!ref) return null;
  let v = String(ref).trim();
  if (!v) return null;
  v = v.replace(/^minecraft:/, '');
  if (v.startsWith('#')) return null;
  return v;
}

function modelPathFromRef(ref, kind) {
  const clean = String(ref || '').replace(/^minecraft:/, '');
  return `assets/minecraft/models/${kind}/${clean}.json`;
}

function collectModelTextureRefs(modelRef, visited) {
  const refs = [];
  const cleanRef = String(modelRef || '').replace(/^minecraft:/, '');
  if (visited.has(cleanRef)) return refs;
  visited.add(cleanRef);

  const modelPath = cleanRef.includes('/')
    ? `assets/minecraft/models/${cleanRef}.json`
    : modelPathFromRef(cleanRef, 'item');
  const raw = readJarEntryText(modelPath);
  if (!raw) return refs;

  let model;
  try {
    model = JSON.parse(raw);
  } catch {
    return refs;
  }

  if (model.parent) {
    const parent = String(model.parent);
    if (parent.startsWith('minecraft:item/') || parent.startsWith('minecraft:block/')) {
      refs.push(...collectModelTextureRefs(parent.replace(/^minecraft:/, ''), visited));
    }
  }

  const textures = model.textures && typeof model.textures === 'object' ? model.textures : {};
  const orderedKeys = ['layer0', 'layer1', 'layer2', 'particle', 'all', 'side', 'top', 'front', 'end'];
  for (const k of orderedKeys) {
    const t = normalizeTextureRef(textures[k]);
    if (t) refs.push(t);
  }
  for (const [k, v] of Object.entries(textures)) {
    if (orderedKeys.includes(k)) continue;
    const t = normalizeTextureRef(v);
    if (t) refs.push(t);
  }

  return refs;
}

function buildLocalIconCandidates(itemId) {
  const direct = [
    `assets/minecraft/textures/item/${itemId}.png`,
    `assets/minecraft/textures/block/${itemId}.png`,
    `assets/minecraft/textures/items/${itemId}.png`,
    `assets/minecraft/textures/blocks/${itemId}.png`,
  ];

  const overrides = ITEM_ICON_TEXTURE_OVERRIDES[itemId] || [];
  direct.push(...overrides);

  const aliases = ITEM_ICON_ALIASES[itemId] || [];
  for (const alias of aliases) {
    direct.push(
      `assets/minecraft/textures/item/${alias}.png`,
      `assets/minecraft/textures/block/${alias}.png`,
    );
  }

  const modelRefs = collectModelTextureRefs(`item/${itemId}`, new Set());
  for (const t of modelRefs) {
    direct.push(`assets/minecraft/textures/${t}.png`);
    if (!t.includes('/')) {
      direct.push(`assets/minecraft/textures/item/${t}.png`);
      direct.push(`assets/minecraft/textures/block/${t}.png`);
    }
  }

  direct.push('assets/minecraft/textures/entity/shield/base.png');
  direct.push('assets/minecraft/textures/entity/shield/base_nopattern.png');

  return [...new Set(direct)];
}

function fetchBuffer(url) {
  return new Promise((resolve) => {
    const req = https.get(url, (res) => {
      if (res.statusCode !== 200) {
        res.resume();
        resolve(null);
        return;
      }
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => resolve(Buffer.concat(chunks)));
    });
    req.on('error', () => resolve(null));
    req.setTimeout(5000, () => {
      req.destroy();
      resolve(null);
    });
  });
}

async function fetchCdnItemIcon(itemId) {
  const refs = [];
  const seen = new Set();
  const pushRef = (ref) => {
    if (!ref || seen.has(ref)) return;
    seen.add(ref);
    refs.push(ref);
  };

  const aliases = ITEM_ICON_ALIASES[itemId] || [];
  pushRef(`item/${itemId}.png`);
  pushRef(`block/${itemId}.png`);

  const overrides = ITEM_ICON_TEXTURE_OVERRIDES[itemId] || [];
  for (const p of overrides) {
    const prefix = 'assets/minecraft/textures/';
    const ref = p.startsWith(prefix) ? p.slice(prefix.length) : null;
    if (ref) pushRef(ref);
  }

  for (const a of aliases) {
    pushRef(`item/${a}.png`);
    pushRef(`block/${a}.png`);
  }
  pushRef('entity/shield/base.png');
  pushRef('entity/shield/base_nopattern.png');

  for (const r of refs) {
    const urls = [
      `https://raw.githubusercontent.com/InventivetalentDev/minecraft-assets/refs/heads/${ITEM_TEXTURE_VERSION}/assets/minecraft/textures/${r}`,
      `https://mcasset.cloud/${ITEM_TEXTURE_VERSION}/assets/minecraft/textures/${r}`,
      `https://classic.mcasset.cloud/${ITEM_TEXTURE_VERSION}/assets/minecraft/textures/${r}`,
    ];
    for (const url of urls) {
      const b = await fetchBuffer(url);
      if (b) return b;
    }
  }
  return null;
}

app.get('/api/item-icon/:id', async (req, res) => {
  let itemId = String(req.params.id || '').trim().toLowerCase();
  if (itemId.includes(':')) itemId = itemId.split(':').pop();
  if (!/^[a-z0-9_]+$/.test(itemId)) return res.status(400).send('Invalid item id');

  if (itemIconCache.has(itemId)) {
    const cached = itemIconCache.get(itemId);
    if (!cached) {
      itemIconCache.delete(itemId);
    } else {
      res.set('Content-Type', 'image/png');
      return res.send(Buffer.from(cached));
    }
  }

  let icon = null;
  if (fs.existsSync(SERVER_JAR)) {
    const candidates = buildLocalIconCandidates(itemId);
    for (const p of candidates) {
      const b = readJarEntryBuffer(p);
      if (b && b.length > 0) {
        icon = b;
        break;
      }
    }
  }

  if (!icon) {
    icon = await fetchCdnItemIcon(itemId);
  }

  if (!icon) {
    return res.status(404).send('Not found');
  }

  itemIconCache.set(itemId, Buffer.from(icon));
  res.set('Content-Type', 'image/png');
  res.send(Buffer.from(icon));
});

app.post('/api/map/request-player-positions', (req, res) => {
  refreshServerState();
  if (!serverRunning) return res.json({ ok: false, requested: false, reason: 'not_running' });
  if (!mcProcess || !mcProcess.stdin.writable) {
    return res.json({ ok: false, requested: false, reason: 'no_command_channel' });
  }
  let count = 0;
  for (const name of onlinePlayers) {
    if (sendCommand(`data get entity ${name} Pos`)) count++;
  }
  res.json({ ok: true, requested: true, count });
});

// --- Socket.IO ---

io.on('connection', (socket) => {
  socket.emit('status', getStatus());
  for (const line of logBuffer) {
    socket.emit('log', line);
  }

  socket.on('command', (cmd) => {
    if (!cmd || !serverRunning) return;
    addLog(`> ${cmd}`);
    sendCommand(cmd);
  });
});

// --- Serve frontend ---

app.get('/', (req, res) => {
  res.sendFile(path.join(SERVER_DIR, 'dashboard.html'));
});

// --- Start ---

const PORT = 3000;
refreshServerState();
if (externalServerPid) {
  addLog(`[Dashboard] Detected running Minecraft server (pid ${externalServerPid}).`);
}
server.listen(PORT, () => {
  console.log(`Dashboard running at http://localhost:${PORT}`);
});

process.on('SIGINT', async () => {
  if (serverRunning) {
    console.log('\nStopping Minecraft server...');
    await stopMinecraft();
  }
  process.exit(0);
});
