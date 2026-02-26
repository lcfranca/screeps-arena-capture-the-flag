// ═══════════════════════════════════════════════════════════════════════════════
// CAPTURE THE FLAG — State-of-the-Art Reactive Agent Architecture
// Reference: docs/strategy.md
// ═══════════════════════════════════════════════════════════════════════════════

// ─── IMPORTS ─────────────────────────────────────────────────────────────────
import {
  getObjectsByPrototype,
  findClosestByPath,
  findClosestByRange,
  findInRange,
  getRange,
  getDirection,
  getTicks,
  getCpuTime,
  getTerrainAt,
  getObjectById,
} from 'game/utils';

import { searchPath, CostMatrix } from 'game/path-finder';

import {
  Creep,
  Flag,
  StructureTower,
  StructureContainer,
  StructureSpawn,
  StructureExtension,
  Source,
} from 'game/prototypes';

import { arenaInfo } from 'game';
import { Visual } from 'game/visual';

import {
  ATTACK,
  RANGED_ATTACK,
  HEAL,
  MOVE,
  CARRY,
  WORK,
  TOUGH,
  RESOURCE_ENERGY,
  TOWER_RANGE,
  TOWER_COOLDOWN,
  TERRAIN_WALL,
  TERRAIN_SWAMP,
  ATTACK_POWER,
  RANGED_ATTACK_POWER,
  HEAL_POWER,
  RANGED_HEAL_POWER,
  OK,
} from 'game/constants';

import { BodyPart } from 'arena/season_2/capture_the_flag/basic';

// ─── ROLE CONSTANTS ──────────────────────────────────────────────────────────
const ROLE_VANGUARD  = 'vanguard';
const ROLE_RANGER    = 'ranger';
const ROLE_MEDIC     = 'medic';
const ROLE_SENTINEL  = 'sentinel';

// ─── CONFIGURATION ──────────────────────────────────────────────────────────
const RETREAT_HP_RATIO         = 0.30;
// HP ratio at which a non-medic creep pulls back to the nearest medic for heals.
// Above RETREAT threshold but below this ratio → soft pull-back (not full flee).
const PULLBACK_HP_RATIO        = 0.65;
const INFLUENCE_REFRESH_TICKS  = 3;
const ROLE_REEVAL_TICKS        = 30;
const BODYPART_DEVIATE_RANGE   = 3;
const KITE_FLEE_RANGE          = 3;
const EMERGENCY_FLEE_RANGE     = 10;
const SENTINEL_PATROL_RANGE    = 4;
const TOWER_THREAT_WEIGHT      = 0.20;
const ENEMY_THREAT_RADIUS      = 6;

// Phase boundaries (ticks)
const PHASE_EXPAND_END    = 150;
const PHASE_CONSOLIDATE   = 500;
const PHASE_ASSAULT_END   = 1500;
const TICK_LIMIT           = 2000;

// Tower charging: how full (%) a tower must be before we stop charging it
const TOWER_CHARGE_THRESHOLD = 0.8; // 80% full → stop charging
// Radius around a tower: if a free creep with CARRY enters this range and no
// charger is assigned yet, ONE is assigned exclusively to that tower.
const TOWER_ASSIGN_RADIUS    = 12;
// Max tiles a non-retreating creep deviates to step on an uncaptured flag.
// Kept tiny (2) so combat and advance are not disrupted.
const FLAG_CAPTURE_RADIUS    = 2;

// ─── PERSISTENT STATE (survives across ticks) ────────────────────────────────
const creepRoles          = new Map();  // id → role string
const towerChargeAssigned = new Map();  // towerId → chargerCreepId
const chargerToTower      = new Map();  // chargerCreepId → towerId
const chargerState        = new Map();  // chargerCreepId → 'WITHDRAW'|'DELIVER'
const creepTargets        = new Map();  // creepId → target {x,y} set by commandLayer each tick
// ONE shared focus target computed by commandLayer — all attackers prefer this enemy.
// Concentrates burst damage to break through enemy heals.
let globalFocusTarget  = null;
let influenceMatrix    = null;
let lastInfluenceTick  = -Infinity;
let initialized        = false;

// ─── DIAGNOSTIC / METRICS STATE ────────────────────────────────────────────────
const diag = {
  startRoster:      null,    // snapshot of initial role counts
  spawnEvents:      [],      // {tick, body, role}
  deathEvents:      [],      // {tick, role, hp}
  flagEvents:       [],      // {tick, type:'capture'|'lose', flag}
  actionCounts:     {},      // role → {move,attack,heal,harvest,idle}
  cpuSamples:       [],      // ns per tick
  idleTicks:        {},      // creep.id → count of idle ticks
  lastFlagSnapshot: null,    // previous tick's flag my/enemy counts
  gameDumped:       false,
};

// ─── PER-TICK WORLD STATE (refreshed every tick) ─────────────────────────────
let myCreeps      = [];
let enemies       = [];
let allFlags      = [];
let myFlag        = null;
let enemyFlags    = [];
let neutralFlags  = [];
let allTowers     = [];
let myTowers      = [];
let enemyTowers   = [];
let containers    = [];
let bodyParts     = [];
let tick          = 0;
// per-tick action tracking (for idle detection)
const tickActions = new Map(); // creep.id → action string this tick

// ═══════════════════════════════════════════════════════════════════════════════
//  1 · SENSE LAYER — World State Refresh
// ═══════════════════════════════════════════════════════════════════════════════

function refreshWorldState() {
  tick = getTicks();
  tickActions.clear();

  // ── Creeps ────────────────────────────────────────────
  const allCreeps = getObjectsByPrototype(Creep);
  const prevMyIds = new Set(myCreeps.map(c => c.id));
  myCreeps = allCreeps.filter(c => c.my);
  enemies  = allCreeps.filter(c => !c.my);

  // Death detection: creeps that vanished since last tick
  const aliveIds = new Set(myCreeps.map(c => c.id));
  for (const id of prevMyIds) {
    if (!aliveIds.has(id)) {
      const role = creepRoles.get(id) || 'unknown';
      diag.deathEvents.push({ tick, id, role });
      creepRoles.delete(id);
      // Release tower charge assignment if this creep was a charger
      const tid = chargerToTower.get(id);
      if (tid) towerChargeAssigned.delete(tid);
      chargerToTower.delete(id);
      chargerState.delete(id);
    }
  }

  // ── Flags ─────────────────────────────────────────────
  allFlags     = getObjectsByPrototype(Flag);
  myFlag       = allFlags.find(f => f.my === true) || null;
  enemyFlags   = allFlags.filter(f => f.my === false);
  neutralFlags = allFlags.filter(f => f.my === undefined);

  // Flag capture/loss detection
  const curMy  = allFlags.filter(f => f.my === true).length;
  const curEn  = allFlags.filter(f => f.my === false).length;
  if (diag.lastFlagSnapshot) {
    const { my: prevMy, enemy: prevEn } = diag.lastFlagSnapshot;
    if (curMy > prevMy)  diag.flagEvents.push({ tick, type: 'capture', myCount: curMy });
    if (curMy < prevMy)  diag.flagEvents.push({ tick, type: 'lose',    myCount: curMy });
    if (curEn > prevEn)  diag.flagEvents.push({ tick, type: 'enemy_captured', enemyCount: curEn });
  }
  diag.lastFlagSnapshot = { my: curMy, enemy: curEn };

  // ── Structures ────────────────────────────────────────
  allTowers    = getObjectsByPrototype(StructureTower);
  myTowers     = allTowers.filter(t => t.my === true);
  enemyTowers  = allTowers.filter(t => t.my === false);
  containers   = getObjectsByPrototype(StructureContainer);
  // Energy supply for towers is in StructureContainers near each tower.
  // Source objects require WORK to harvest (none of our creeps have WORK).

  bodyParts  = getObjectsByPrototype(BodyPart);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  2 · BODY INTROSPECTION HELPERS
// ═══════════════════════════════════════════════════════════════════════════════

function countParts(creep, type) {
  return creep.body.filter(p => p.type === type).length;
}

function countActive(creep, type) {
  return creep.body.filter(p => p.type === type && p.hits > 0).length;
}

function hasActive(creep, type) {
  return creep.body.some(p => p.type === type && p.hits > 0);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  3 · ROLE CLASSIFICATION & ASSIGNMENT
// ═══════════════════════════════════════════════════════════════════════════════

function classifyCreep(creep) {
  const a = countParts(creep, ATTACK);
  const r = countParts(creep, RANGED_ATTACK);
  const h = countParts(creep, HEAL);

  // Medic: primarily HEAL
  if (h > 0 && h >= a && h >= r) return ROLE_MEDIC;

  // Ranger: primarily RANGED_ATTACK
  if (r > 0 && r >= a) return ROLE_RANGER;

  // Vanguard: primarily ATTACK (or any combat creep)
  if (a > 0) return ROLE_VANGUARD;

  // Fallbacks based on any part
  if (h > 0) return ROLE_MEDIC;
  if (r > 0) return ROLE_RANGER;

  // CARRY/TOUGH/MOVE-only creeps: treat as vanguard (charger-eligible)
  return ROLE_VANGUARD;
}

function assignRoles() {
  const counts = {
    [ROLE_VANGUARD]: 0, [ROLE_RANGER]: 0, [ROLE_MEDIC]: 0, [ROLE_SENTINEL]: 0,
  };

  for (const creep of myCreeps) {
    const role = classifyCreep(creep);
    creepRoles.set(creep.id, role);
    counts[role]++;
  }

  // Snapshot initial roster for diagnostics
  if (!diag.startRoster) {
    diag.startRoster = { ...counts, total: myCreeps.length };
    for (const role of Object.keys(counts)) {
      diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
    }
    console.log(`[INIT T${tick}] Roster: ${JSON.stringify(diag.startRoster)}`);
  }

  // Promote 1 vanguard to sentinel for home flag defense
  if (counts[ROLE_SENTINEL] === 0) {
    const pool = myCreeps
      .filter(c => creepRoles.get(c.id) === ROLE_VANGUARD)
      .sort((a, b) => countParts(b, TOUGH) - countParts(a, TOUGH));
    if (pool.length > 2 && myFlag) {
      const sentinel = pool.reduce((best, c) =>
        getRange(c, myFlag) < getRange(best, myFlag) ? c : best
      );
      creepRoles.set(sentinel.id, ROLE_SENTINEL);
      counts[ROLE_SENTINEL]++;
      counts[ROLE_VANGUARD]--;
    }
  }
}

function reevaluateRoles() {
  // Prune dead creeps
  const aliveIds = new Set(myCreeps.map(c => c.id));
  for (const id of creepRoles.keys()) {
    if (!aliveIds.has(id)) {
      creepRoles.delete(id);
      const t2id = chargerToTower.get(id);
      if (t2id) towerChargeAssigned.delete(t2id);
      chargerToTower.delete(id);
      chargerState.delete(id);
    }
  }

  const counts = {};
  for (const role of creepRoles.values()) {
    counts[role] = (counts[role] || 0) + 1;
  }

  // No vanguards? Promote strongest ranger
  if (!counts[ROLE_VANGUARD] && (counts[ROLE_RANGER] || 0) > 1) {
    const rangers = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_RANGER);
    const best = rangers.sort((a, b) => countParts(b, ATTACK) - countParts(a, ATTACK))[0];
    if (best) creepRoles.set(best.id, ROLE_VANGUARD);
  }

  // No medics? Convert a ranger that has HEAL parts
  if (!counts[ROLE_MEDIC] && (counts[ROLE_RANGER] || 0) > 2) {
    const candidates = myCreeps.filter(c =>
      creepRoles.get(c.id) === ROLE_RANGER && countParts(c, HEAL) > 0
    );
    if (candidates.length > 0) {
      const best = candidates.sort((a, b) => countParts(b, HEAL) - countParts(a, HEAL))[0];
      creepRoles.set(best.id, ROLE_MEDIC);
    }
  }

  // Sentinel died? Promote nearest to flag
  if (!counts[ROLE_SENTINEL] && myFlag) {
    const pool = myCreeps.filter(c => {
      const r = creepRoles.get(c.id);
      return r === ROLE_VANGUARD || r === ROLE_RANGER;
    });
    if (pool.length > 3) {
      const closest = pool.reduce((b, c) =>
        getRange(c, myFlag) < getRange(b, myFlag) ? c : b
      );
      creepRoles.set(closest.id, ROLE_SENTINEL);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  4 · THREAT ASSESSMENT ENGINE
// ═══════════════════════════════════════════════════════════════════════════════

function threatScore(enemy) {
  const atk = countActive(enemy, ATTACK);
  const rng = countActive(enemy, RANGED_ATTACK);
  const hea = countActive(enemy, HEAL);
  return (atk * ATTACK_POWER) + (rng * RANGED_ATTACK_POWER) + (hea * HEAL_POWER)
       + (enemy.hits / enemy.hitsMax);
}

/**
 * Focus-fire target selection with kill-priority heuristic.
 * Order: kill-secured → healers → lowest HP ratio → highest threat.
 */
function selectFocusTarget(fromPos, eligible) {
  if (eligible.length === 0) return null;
  if (eligible.length === 1) return eligible[0];

  const myMedics = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
  return eligible.slice().sort((a, b) => {
    // 0. Enemy threatening a medic (within 4 tiles) → eliminate first
    const aThreatsMedic = myMedics.some(m => getRange(a, m) <= 4);
    const bThreatsMedic = myMedics.some(m => getRange(b, m) <= 4);
    if (aThreatsMedic !== bThreatsMedic) return aThreatsMedic ? -1 : 1;
    // 1. Kill-secured (< 100 HP)
    const aLow = a.hits <= 100;
    const bLow = b.hits <= 100;
    if (aLow !== bLow) return aLow ? -1 : 1;

    // 1b. "Unhealed" bonus: enemy with no friendly healer within range 5 is easier to kill.
    // Prefer un-sustained targets so we can actually eliminate them despite enemy heals.
    const aUnhealed = !enemies.some(e => e.id !== a.id && countActive(e, HEAL) > 0 && getRange(e, a) <= 5);
    const bUnhealed = !enemies.some(e => e.id !== b.id && countActive(e, HEAL) > 0 && getRange(e, b) <= 5);
    if (aUnhealed !== bUnhealed) return aUnhealed ? -1 : 1;

    // 2. Healers first (remove sustain)
    const aH = countActive(a, HEAL) > 0;
    const bH = countActive(b, HEAL) > 0;
    if (aH !== bH) return aH ? -1 : 1;

    // 3. Lowest HP ratio
    const rA = a.hits / a.hitsMax;
    const rB = b.hits / b.hitsMax;
    if (rA !== rB) return rA - rB;

    // 4. Highest threat
    return threatScore(b) - threatScore(a);
  })[0];
}

// ═══════════════════════════════════════════════════════════════════════════════
//  5 · INFLUENCE MAP (CostMatrix-Based Potential Field)
// ═══════════════════════════════════════════════════════════════════════════════

function buildInfluenceMap() {
  const cm = new CostMatrix();

  // ── Enemy threat field ─────────────────────────────────
  for (const enemy of enemies) {
    const t = Math.max(1, threatScore(enemy));
    for (let dx = -ENEMY_THREAT_RADIUS; dx <= ENEMY_THREAT_RADIUS; dx++) {
      for (let dy = -ENEMY_THREAT_RADIUS; dy <= ENEMY_THREAT_RADIUS; dy++) {
        const nx = enemy.x + dx;
        const ny = enemy.y + dy;
        if (nx < 0 || nx > 99 || ny < 0 || ny > 99) continue;
        const dist = Math.max(Math.abs(dx), Math.abs(dy));
        if (dist > ENEMY_THREAT_RADIUS) continue;
        if (getTerrainAt({ x: nx, y: ny }) === TERRAIN_WALL) continue;
        const penalty = Math.min(200, Math.floor(t / (dist + 1) * 0.4));
        const base = getTerrainAt({ x: nx, y: ny }) === TERRAIN_SWAMP ? 10 : 2;
        cm.set(nx, ny, Math.min(254, Math.max(cm.get(nx, ny), base + penalty)));
      }
    }
  }

  // ── Enemy tower danger zone ────────────────────────────
  for (const tower of enemyTowers) {
    const energy = tower.store ? tower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    if (energy <= 0) continue;
    for (let dx = -TOWER_RANGE; dx <= TOWER_RANGE; dx++) {
      for (let dy = -TOWER_RANGE; dy <= TOWER_RANGE; dy++) {
        const nx = tower.x + dx;
        const ny = tower.y + dy;
        if (nx < 0 || nx > 99 || ny < 0 || ny > 99) continue;
        const dist = Math.max(Math.abs(dx), Math.abs(dy));
        if (dist > TOWER_RANGE) continue;
        if (getTerrainAt({ x: nx, y: ny }) === TERRAIN_WALL) continue;
        const dmg = Math.max(0, 1000 - 50 * (dist - 1));
        const penalty = Math.min(200, Math.floor(dmg * TOWER_THREAT_WEIGHT));
        cm.set(nx, ny, Math.min(254, Math.max(cm.get(nx, ny), penalty)));
      }
    }
  }

  // ── Arena edge penalty — prevents kiting/fleeing into walls/corners ─────────
  // Tiles within WALL_REPEL_DIST of any edge get a progressive cost penalty.
  // This biases ALL searchPath(flee) calls toward the center of the map.
  const WALL_REPEL_DIST = 8;
  for (let x = 0; x < 100; x++) {
    for (let y = 0; y < 100; y++) {
      if (getTerrainAt({ x, y }) === TERRAIN_WALL) continue;
      const edgeDist = Math.min(x, y, 99 - x, 99 - y);
      if (edgeDist < WALL_REPEL_DIST) {
        const penalty = Math.floor((WALL_REPEL_DIST - edgeDist) * 10);
        cm.set(x, y, Math.min(254, cm.get(x, y) + penalty));
      }
    }
  }

  // ── Ally stacking avoidance ────────────────────────────
  for (const ally of myCreeps) {
    const cur = cm.get(ally.x, ally.y);
    cm.set(ally.x, ally.y, Math.min(254, cur + 4));
  }

  influenceMatrix   = cm;
  lastInfluenceTick = tick;
}

function getInfluenceMap() {
  if (!influenceMatrix || tick - lastInfluenceTick >= INFLUENCE_REFRESH_TICKS) {
    buildInfluenceMap();
  }
  return influenceMatrix;
}

function pathOpts(flee = false) {
  return {
    costMatrix: getInfluenceMap(),
    flee,
    plainCost: 2,
    swampCost: 10,
    maxOps: 2000,
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//  6 · PHASE CONTROLLER
// ═══════════════════════════════════════════════════════════════════════════════

function getPhase() {
  if (tick <= PHASE_EXPAND_END)  return 1;
  if (tick <= PHASE_CONSOLIDATE) return 2;
  if (tick <= PHASE_ASSAULT_END) return 3;
  return 4;
}

function myFlagCount()    { return allFlags.filter(f => f.my === true).length; }
function enemyFlagCount() { return allFlags.filter(f => f.my === false).length; }

// ═══════════════════════════════════════════════════════════════════════════════
//  7 · RETREAT PROTOCOL (Behavior Layer 5)
// ═══════════════════════════════════════════════════════════════════════════════

function shouldRetreat(creep) {
  if (creep.hits >= creep.hitsMax * RETREAT_HP_RATIO) return false;
  // Only retreat if medics are alive to heal us at the rally point.
  // With no medics, retreating to myFlag is permanent — the creep idles forever
  // because HP never recovers. Better to hold and deal damage.
  const medicsAlive = myCreeps.some(c => creepRoles.get(c.id) === ROLE_MEDIC);
  return medicsAlive;
}

/**
 * Soft pull-back: front-line creep is moderately damaged and has no medic cover.
 * The creep steps toward the nearest medic to receive heals, then re-engages.
 * This is NOT a full retreat — the creep still fights while moving.
 */
function shouldPullBack(creep) {
  if (shouldRetreat(creep)) return false;                          // full retreat handles this
  const role = creepRoles.get(creep.id);
  if (role === ROLE_MEDIC || role === ROLE_SENTINEL) return false; // medics don't pull back
  const ratio = creep.hits / creep.hitsMax;
  if (ratio > PULLBACK_HP_RATIO) return false;                     // still healthy
  // Suppress pull-back if a medic is already adjacent (healing happening)
  return !myCreeps.some(c => creepRoles.get(c.id) === ROLE_MEDIC && getRange(creep, c) <= 1);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  9 · COMMANDER LAYER — Global target assignment (runs once per tick)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Picks ONE global objective and writes per-creep movement targets.
 * All combat creeps share the same directive — no conflicting objectives.
 * See docs/strategy.md §3 for architecture rationale.
 */
function commandLayer() {
  // Net-advantage score: (enemies near flag) − (allies near flag).
  // Lower = easier to take/hold. Naturally stable: as our creeps approach a flag,
  // their presence reduces that flag's score, self-reinforcing the choice.
  const centroid = squadCentroid() || { x: 50, y: 50 };
  function leastDefended(flags) {
    return flags.reduce((best, f) => {
      const sf = findInRange(f, enemies, 8).length - findInRange(f, myCreeps, 8).length;
      const sb = findInRange(best, enemies, 8).length - findInRange(best, myCreeps, 8).length;
      if (sf !== sb) return sf < sb ? f : best;
      return getRange(centroid, f) <= getRange(centroid, best) ? f : best;
    });
  }

  let objective = null;

  // Priority: expand neutrals → push enemy → hold own
  if (neutralFlags.length > 0) {
    objective = leastDefended(neutralFlags);
  } else if (enemyFlags.length > 0) {
    objective = leastDefended(enemyFlags);
  } else {
    objective = myFlag;
  }

  for (const creep of myCreeps) {
    if (chargerToTower.has(creep.id)) continue;
    const role = creepRoles.get(creep.id);
    creepTargets.set(creep.id, role === ROLE_SENTINEL ? (myFlag || objective) : objective);
  }

  // ── Global focus target ────────────────────────────────────────────
  // Use squad centroid (not map center) so focus is on enemies near the fight.
  if (enemies.length > 0) {
    const sqCenter = squadCentroid() || { x: 50, y: 50 };
    globalFocusTarget = selectFocusTarget(sqCenter, enemies);
  } else {
    globalFocusTarget = null;
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  ACTION RECORDING HELPER
// ═══════════════════════════════════════════════════════════════════════════════
function recordAction(creep, action) {
  tickActions.set(creep.id, action);
  const role = creepRoles.get(creep.id) || 'unknown';
  if (!diag.actionCounts[role]) {
    diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
  }
  const key = (['move','attack','heal','harvest'].includes(action)) ? action : 'idle';
  diag.actionCounts[role][key]++;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  10b · TOWER CHARGING — Dedicated charger system (one per hungry tower)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Centroid (average position) of all non-medic combat creeps.
 * Used by Medics and Rangers to stay near the fight.
 */
function squadCentroid() {
  const squad = myCreeps.filter(c => {
    const r = creepRoles.get(c.id);
    return r === ROLE_VANGUARD || r === ROLE_RANGER || r === ROLE_SENTINEL;
  });
  if (squad.length === 0) return null;
  const ax = Math.round(squad.reduce((s, c) => s + c.x, 0) / squad.length);
  const ay = Math.round(squad.reduce((s, c) => s + c.y, 0) / squad.length);
  return { x: ax, y: ay };
}

/**
 * Each tick: release stale assignments, then assign ONE free CARRY creep per
 * hungry tower that has at least one candidate within TOWER_ASSIGN_RADIUS.
 *
 * Energy supply: StructureContainer objects near towers.
 * (Source objects require WORK to harvest — none of our creeps have WORK.)
 */
function assignTowerChargers() {
  // Release: dead charger or tower now charged
  for (const [towerId, cpId] of [...towerChargeAssigned.entries()]) {
    const creep = myCreeps.find(c => c.id === cpId);
    if (!creep) {
      towerChargeAssigned.delete(towerId);
      chargerToTower.delete(cpId);
      chargerState.delete(cpId);
      continue;
    }
    const tower = getObjectById(towerId);
    if (!tower) {
      towerChargeAssigned.delete(towerId);
      chargerToTower.delete(cpId);
      chargerState.delete(cpId);
      continue;
    }
    const used = tower.store ? tower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    const cap  = tower.store ? tower.store.getCapacity(RESOURCE_ENERGY) : 1;
    if (cap > 0 && (used / cap) >= TOWER_CHARGE_THRESHOLD) {
      // Tower charged → release charger back to combat
      towerChargeAssigned.delete(towerId);
      chargerToTower.delete(cpId);
      chargerState.delete(cpId);
    }
  }

  // Assign: one free charger per still-hungry tower
  for (const tower of myTowers) {
    if (towerChargeAssigned.has(tower.id)) continue;
    const used = tower.store ? tower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    const cap  = tower.store ? tower.store.getCapacity(RESOURCE_ENERGY) : 1;
    if (cap === 0 || (used / cap) >= TOWER_CHARGE_THRESHOLD) continue;

    // Only assign if there is a container with energy near this tower
    const energySrc = containers.filter(c =>
      c.store && c.store.getUsedCapacity(RESOURCE_ENERGY) > 0
    );
    if (energySrc.length === 0) continue;

    // Candidate: free CARRY creep within TOWER_ASSIGN_RADIUS of tower
    const candidates = myCreeps.filter(c =>
      !chargerToTower.has(c.id) &&
      hasActive(c, CARRY) &&
      getRange(c, tower) <= TOWER_ASSIGN_RADIUS
    );
    if (candidates.length === 0) continue;

    const chosen = findClosestByRange(tower, candidates);
    if (!chosen) continue;
    towerChargeAssigned.set(tower.id, chosen.id);
    chargerToTower.set(chosen.id, tower.id);
    chargerState.set(chosen.id, 'WITHDRAW');
  }
}

/**
 * Behavior for an explicitly assigned tower charger.
 * FSM: WITHDRAW (fetch energy from closest container) → DELIVER (transfer to tower).
 * Steps on BodyParts opportunistically when they are close by.
 */
function behaviorCharger(creep) {
  const towerId = chargerToTower.get(creep.id);
  if (!towerId) return;
  const tower = getObjectById(towerId);
  if (!tower) {
    chargerToTower.delete(creep.id);
    chargerState.delete(creep.id);
    return;
  }

  const energy = creep.store ? (creep.store.getUsedCapacity(RESOURCE_ENERGY) || 0) : 0;
  const free   = creep.store ? (creep.store.getFreeCapacity(RESOURCE_ENERGY) || 0)  : 0;
  let   state  = chargerState.get(creep.id) || 'WITHDRAW';

  // Find closest container with energy (use tower position for cache efficiency)
  const energyContainers = containers.filter(c =>
    c.store && c.store.getUsedCapacity(RESOURCE_ENERGY) > 0
  );
  const src = energyContainers.length > 0 ? findClosestByRange(tower, energyContainers) : null;

  // State transitions
  if (state === 'WITHDRAW' && free <= 0)   { state = 'DELIVER'; }
  if (state === 'DELIVER'  && energy <= 0) { state = 'WITHDRAW'; }
  chargerState.set(creep.id, state);

  if (state === 'WITHDRAW') {
    if (!src) {
      // No container energy available — deliver carry if any, else wait near tower
      if (energy > 0) {
        chargerState.set(creep.id, 'DELIVER');
        if (getRange(creep, tower) <= 1) {
          creep.transfer(tower, RESOURCE_ENERGY);
          recordAction(creep, 'harvest');
        } else {
          creep.moveTo(tower);
          recordAction(creep, 'move');
        }
      } else {
        // Step on body part nearby while containers refill
        const bp = bodyParts.length > 0 ? findClosestByRange(creep, bodyParts) : null;
        if (bp && getRange(creep, bp) <= 6) {
          creep.moveTo(bp);
        } else if (getRange(creep, tower) > 2) {
          creep.moveTo(tower);
        }
        recordAction(creep, 'move');
      }
      return;
    }
    if (getRange(creep, src) <= 1) {
      creep.withdraw(src, RESOURCE_ENERGY);
      recordAction(creep, 'harvest');
    } else {
      // Move toward container; body parts on path are auto-collected on adjacent tile
      creep.moveTo(src);
      recordAction(creep, 'move');
    }
    return;
  }

  // DELIVER state: bring energy to tower
  if (getRange(creep, tower) <= 1) {
    creep.transfer(tower, RESOURCE_ENERGY);
    // After delivering, divert to step on any close body part
    const bp = bodyParts.length > 0 ? findClosestByRange(creep, bodyParts) : null;
    if (bp && getRange(creep, bp) <= 4) creep.moveTo(bp);
    recordAction(creep, 'harvest');
  } else {
    creep.moveTo(tower);
    recordAction(creep, 'move');
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  11 · COMBAT ACTION — Decoupled from movement (fills the ATTACK/HEAL slot)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Executes the creep's combat action this tick.
 * NEVER calls moveTo() or move(). Returns action type or null.
 * Runs for every creep including chargers (they can fight while fetching energy).
 */
function doCombatAction(creep) {
  const role = creepRoles.get(creep.id);

  // Retreating: highest priority — self-heal or shoot while fleeing
  if (shouldRetreat(creep)) {
    if (hasActive(creep, HEAL)) { creep.heal(creep); return 'heal'; }
    if (hasActive(creep, RANGED_ATTACK)) {
      const inR3 = findInRange(creep, enemies, 3);
      if (inR3.length >= 3) { creep.rangedMassAttack(); return 'attack'; }
      if (inR3.length > 0) {
        const t = selectFocusTarget(creep, inR3);
        if (t) { creep.rangedAttack(t); return 'attack'; }
      }
    }
    return null;
  }

  if (role === ROLE_MEDIC) {
    // Medics: healing always beats attacking
    if (hasActive(creep, HEAL)) {
      const damaged = myCreeps.filter(c => c.hits < c.hitsMax && c.id !== creep.id);
      const adjDmg  = findInRange(creep, damaged, 1);
      const nearDmg = findInRange(creep, damaged, 3);
      // Heal by HP ratio (most critical first), not absolute HP
      if (adjDmg.length > 0) {
        const t = adjDmg.reduce((b, c) => (c.hits/c.hitsMax) < (b.hits/b.hitsMax) ? c : b);
        creep.heal(t); return 'heal';
      }
      if (nearDmg.length > 0) {
        const t = nearDmg.reduce((b, c) => (c.hits/c.hitsMax) < (b.hits/b.hitsMax) ? c : b);
        creep.rangedHeal(t); return 'heal';
      }
      if (creep.hits < creep.hitsMax) { creep.heal(creep); return 'heal'; }
    }
    // Nothing to heal → attack adjacent enemy
    if (hasActive(creep, ATTACK)) {
      const adj = findInRange(creep, enemies, 1);
      if (adj.length > 0) {
        const t = selectFocusTarget(creep, adj);
        if (t) { creep.attack(t); return 'attack'; }
      }
    }
    return null;
  }

  // Combat roles (vanguard, ranger, sentinel): melee > ranged > self-heal
  if (hasActive(creep, ATTACK)) {
    const adj = findInRange(creep, enemies, 1);
    if (adj.length > 0) {
      // Prefer the global shared focus target to burst through enemy heals
      const t = (globalFocusTarget && adj.some(e => e.id === globalFocusTarget.id))
        ? globalFocusTarget
        : selectFocusTarget(creep, adj);
      if (t) { creep.attack(t); return 'attack'; }
    }
  }
  if (hasActive(creep, RANGED_ATTACK)) {
    const inR3 = findInRange(creep, enemies, 3);
    if (inR3.length > 0) {
      if (inR3.length >= 3) { creep.rangedMassAttack(); return 'attack'; }
      // Prefer global focus target; fall back to individual selection
      const t = (globalFocusTarget && inR3.some(e => e.id === globalFocusTarget.id))
        ? globalFocusTarget
        : selectFocusTarget(creep, inR3);
      if (t) { creep.rangedAttack(t); return 'attack'; }
    }
  }
  // Opportunistic: heal an adjacent ally or self if idle
  if (hasActive(creep, HEAL)) {
    const damaged = myCreeps.filter(c => c.hits < c.hitsMax);
    const adj = findInRange(creep, damaged, 1);
    if (adj.length > 0) { creep.heal(adj.reduce((b, c) => c.hits < b.hits ? c : b)); return 'heal'; }
    if (creep.hits < creep.hitsMax) { creep.heal(creep); return 'heal'; }
  }
  return null;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  12 · MOVE ACTION — Priority stack (fills the MOVE slot)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Executes the creep's movement this tick.
 * NEVER calls attack(), heal(), rangedAttack(), or rangedHeal().
 * Strictly ordered priority stack — first matching rule wins.
 * A creep ALWAYS moves (static = bug). Formation is a soft pull, never a block.
 */
function doMoveAction(creep) {
  const role = creepRoles.get(creep.id);

  // P0: Emergency retreat — always wins
  if (shouldRetreat(creep)) {
    const nearby = findInRange(creep, enemies, 8);
    if (nearby.length > 0) {
      const result = searchPath(
        creep,
        nearby.map(e => ({ pos: e, range: EMERGENCY_FLEE_RANGE })),
        pathOpts(true),
      );
      if (result.path.length > 0) {
        creep.move(getDirection(result.path[0].x - creep.x, result.path[0].y - creep.y));
        return;
      }
    }
    // Move toward nearest medic so we can be healed and re-engage.
    // Falling back to myFlag strands creeps far from medics forever.
    const medics = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
    if (medics.length > 0) {
      const nearest = findClosestByRange(creep, medics);
      if (nearest) { creep.moveTo(nearest, pathOpts()); return; }
    }
    if (myFlag) creep.moveTo(myFlag, pathOpts());
    return;
  }

  // P0.5: Pull-back — moderately damaged, no adjacent medic → step toward nearest medic.
  // The creep still fires via doCombatAction (combat slot is independent).
  // Once a medic is adjacent (and thus healing), pull-back condition clears.
  if (shouldPullBack(creep)) {
    const medics = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
    if (medics.length > 0) {
      const nearest = findClosestByRange(creep, medics);
      if (nearest && getRange(creep, nearest) > 1) {
        creep.moveTo(nearest, pathOpts());
        return;
      }
    }
  }

  // P1: Body part on same tile — auto-collecting, no move needed
  if (bodyParts.some(b => b.x === creep.x && b.y === creep.y)) return;

  // P2: Body part within range 1 — micro-divert (zero cost since we're adjacent)
  if (bodyParts.length > 0) {
    const adj = findInRange(creep, bodyParts, 1);
    if (adj.length > 0) {
      const prio = { [HEAL]: 4, [ATTACK]: 3, [RANGED_ATTACK]: 2, [MOVE]: 1 };
      adj.sort((a, b) => (prio[b.type] || 0) - (prio[a.type] || 0));
      creep.moveTo(adj[0]);
      return;
    }
  }

  // P2b: Uncaptured flag within tiny radius — step on it without breaking combat.
  // Safety guard: only divert if the area is clear (no enemies within range 4)
  // OR a friendly medic is within rangedHeal range (≤ 3), ensuring the creep
  // won't walk unsupported into an enemy cluster to grab a flag.
  const uncaptured = [...neutralFlags, ...enemyFlags];
  if (uncaptured.length > 0) {
    const nearFlag = findInRange(creep, uncaptured, FLAG_CAPTURE_RADIUS);
    if (nearFlag.length > 0) {
      const enemiesNear    = findInRange(creep, enemies, 4);
      const medicCoverage  = myCreeps.some(
        c => creepRoles.get(c.id) === ROLE_MEDIC && getRange(creep, c) <= 3
      );
      if (enemiesNear.length === 0 || medicCoverage) {
        const closest = findClosestByRange(creep, nearFlag);
        if (closest) { creep.moveTo(closest); return; }
      }
    }
  }

  // P3: Role-specific local movement
  if (role === ROLE_MEDIC) {
    const frontline = myCreeps.filter(c => {
      const r = creepRoles.get(c.id);
      return r !== ROLE_MEDIC && c.id !== creep.id;
    });

    // P3-M1: Creep pulling back (damaged, needs heals) → intercept at high priority
    const pullingBack = frontline.filter(c => shouldPullBack(c));
    if (pullingBack.length > 0) {
      const worst = pullingBack.reduce((b, c) => (c.hits / c.hitsMax) < (b.hits / b.hitsMax) ? c : b);
      if (getRange(creep, worst) > 1) { creep.moveTo(worst, pathOpts()); return; }
      return;
    }

    // P3-M2: Chase most-damaged ally unconditionally.
    // The influence map (pathOpts) already penalizes tiles near enemies, so the path
    // naturally routes around hot zones. The old "allyInDanger" stop was preventing
    // medics from healing anyone in active combat — i.e., 100% of the time.
    // Medics must stay adjacent (range 1 = full heal) or at most range 3 (rangedHeal).
    const damaged = frontline.filter(c => c.hits < c.hitsMax);
    if (damaged.length > 0) {
      const worst = damaged.reduce((b, c) => (c.hits / c.hitsMax) < (b.hits / b.hitsMax) ? c : b);
      if (getRange(creep, worst) > 1) { creep.moveTo(worst, pathOpts()); return; }
      return;
    }

    // P3-M3: Nobody damaged → pre-position at range 2 of the most-forward combat ally.
    // "Most-forward" = closest to enemy centroid. Being at range 2 means:
    //   • Vanguard is body-blocking between medic and enemies
    //   • Full heal (range 1) reachable in 1 move step
    //   • rangedHeal (range 3) available immediately without moving
    if (frontline.length > 0 && enemies.length > 0) {
      const eCx = Math.round(enemies.reduce((s, e) => s + e.x, 0) / enemies.length);
      const eCy = Math.round(enemies.reduce((s, e) => s + e.y, 0) / enemies.length);
      const frontmost = frontline.reduce((b, c) =>
        getRange(c, {x: eCx, y: eCy}) < getRange(b, {x: eCx, y: eCy}) ? c : b
      );
      const d = getRange(creep, frontmost);
      if (d > 2) { creep.moveTo(frontmost, pathOpts()); return; }
      return; // in position
    }

    // P3-M4: Fallback — follow squad centroid
    const centroid = squadCentroid();
    if (centroid && getRange(creep, centroid) > 3) {
      creep.moveTo(centroid, pathOpts()); return;
    }
    const obj = creepTargets.get(creep.id);
    if (obj) creep.moveTo(obj, pathOpts());
    return;
  }

  if (role === ROLE_RANGER) {
    // Kite: react when enemy within range 4.
    // Flee to range 4 (not 5) to stay within rangedHeal coverage of medics.
    // Bias kite direction: flee toward nearest medic when possible so rangers
    // never drift out of heal range during combat.
    const inR4 = findInRange(creep, enemies, 4);
    if (inR4.length > 0) {
      const myMedics = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
      const nearestMedic = myMedics.length > 0 ? findClosestByRange(creep, myMedics) : null;
      // If we are already far from medics, kite toward them (flee from enemies
      // but the cost matrix already biases toward ally positions).
      if (nearestMedic && getRange(creep, nearestMedic) > 4) {
        // Move toward medic— influence map still penalizes enemy tiles
        creep.moveTo(nearestMedic, pathOpts());
        return;
      }
      const result = searchPath(
        creep,
        inR4.map(e => ({ pos: e, range: 4 })),
        pathOpts(true),
      );
      if (result.path.length > 0) {
        creep.move(getDirection(result.path[0].x - creep.x, result.path[0].y - creep.y));
      }
      return;
    }
    // Advance toward nearest enemy until we reach ideal firing range (3),
    // but only if squad is nearby (ally within r8). Isolated ranger rejoins first.
    if (enemies.length > 0) {
      const nearest = findClosestByRange(creep, enemies);
      const squadNear = myCreeps.filter(c => c.id !== creep.id && getRange(creep, c) <= 8).length > 0;
      if (nearest && getRange(creep, nearest) > 3 && squadNear) {
        creep.moveTo(nearest, pathOpts()); return;
      }
    }
    // Not in range or isolated: anchor to nearest medic if available, else centroid
    const myMedicsR = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
    const anchorMedic = myMedicsR.length > 0 ? findClosestByRange(creep, myMedicsR) : null;
    if (anchorMedic && getRange(creep, anchorMedic) > 3) {
      creep.moveTo(anchorMedic, pathOpts()); return;
    }
    const centroid = squadCentroid();
    if (centroid && getRange(creep, centroid) > 4) {
      creep.moveTo(centroid, pathOpts()); return;
    }
    const obj = creepTargets.get(creep.id);
    if (obj) creep.moveTo(obj, pathOpts());
    return;
  }

  if (role === ROLE_SENTINEL) {
    // Intercept flag threats first
    const threats = myFlag ? findInRange(myFlag, enemies, 8) : [];
    if (threats.length > 0) {
      const t = selectFocusTarget(creep, threats);
      if (t) { creep.moveTo(t, pathOpts()); return; }
    }

    // Offensive redeploy: home flag is safe AND we are losing flags → join attack.
    // Sentinel contributes DPS instead of idling 1000+ ticks near an uncontested flag.
    const flagBalance = myFlagCount() - enemyFlagCount();
    if (threats.length === 0 && flagBalance < 0 && enemies.length > 0) {
      const target = globalFocusTarget || findClosestByRange(creep, enemies);
      if (target) { creep.moveTo(target, pathOpts()); return; }
    }

    // Patrol near flag
    if (myFlag && getRange(creep, myFlag) > SENTINEL_PATROL_RANGE) {
      creep.moveTo(myFlag, pathOpts());
    }
    return;
  }

  // VANGUARD (and undefined/fallback):
  // Only chase enemies directly if we have local numerical advantage OR are in immediate defense.
  // This prevents the single-vanguard walking into a 14-creep deathball.
  // "Local" = range 6 around this creep.
  const nearEnemies = findInRange(creep, enemies, 5);
  if (nearEnemies.length > 0) {
    const nearAllies = myCreeps.filter(c => c.id !== creep.id && getRange(creep, c) <= 6);
    const inMelee    = findInRange(creep, enemies, 1).length > 0;  // already adjacent — must fight
    // Engage if: in immediate defense OR allies roughly match local enemies
    if (inMelee || nearAllies.length >= nearEnemies.length - 1) {
      const t = selectFocusTarget(creep, nearEnemies);
      if (t) { creep.moveTo(t, pathOpts()); return; }
    }
  }
  // No local engagement: stay cohesive with the squad.
  // Move to commander target, but if we are isolated (no ally within range 8)
  // first close to the squad centroid so the group advances together.
  const centroid = squadCentroid();
  if (centroid && myCreeps.filter(c => c.id !== creep.id && getRange(creep, c) <= 8).length === 0) {
    // Isolated — rejoin squad before pushing forward
    creep.moveTo(centroid, pathOpts());
    return;
  }
  const obj = creepTargets.get(creep.id);
  if (obj) creep.moveTo(obj, pathOpts());
}

// ═══════════════════════════════════════════════════════════════════════════════
//  13 · TICK EXECUTOR — Decoupled combat + movement, no conflicts
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Per-creep execution: fills COMBAT SLOT and MOVE SLOT independently.
 * These two slots NEVER interfere — Screeps allows both per tick.
 * Chargers use behaviorCharger for movement but still fight via doCombatAction.
 */
function executeTick(creep) {
  const combatAct = doCombatAction(creep); // COMBAT SLOT (always)

  if (chargerToTower.has(creep.id)) {
    // Charger movement managed by behaviorCharger (includes its own recordAction)
    behaviorCharger(creep);
    if (combatAct) recordAction(creep, combatAct); // override to reflect combat
    return;
  }

  doMoveAction(creep);                      // MOVE SLOT (always)
  recordAction(creep, combatAct || 'move');
}

// ═══════════════════════════════════════════════════════════════════════════════
//  16 · TOWER CONTROLLER

// ═══════════════════════════════════════════════════════════════════════════════
//  16 · TOWER CONTROLLER
// ═══════════════════════════════════════════════════════════════════════════════

function towerController() {
  for (const tower of myTowers) {
    const energy = tower.store ? tower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    if (energy <= 0 || tower.cooldown > 0) continue;

    const enemiesInRange = findInRange(tower, enemies, TOWER_RANGE);

    if (enemiesInRange.length > 0) {
      // Kill-secured targets first, then closest (max damage via falloff)
      const killable = enemiesInRange.filter(e => e.hits <= 200);
      const target = killable.length > 0
        ? findClosestByRange(tower, killable)
        : findClosestByRange(tower, enemiesInRange);
      if (target) { tower.attack(target); continue; }
    }

    // Heal damaged allies in range
    const alliesInRange = findInRange(tower, myCreeps, TOWER_RANGE);
    const damagedAllies = alliesInRange.filter(c => c.hits < c.hitsMax);
    if (damagedAllies.length > 0) {
      damagedAllies.sort((a, b) => (a.hits / a.hitsMax) - (b.hits / b.hitsMax));
      tower.heal(damagedAllies[0]);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  17 · PULL CHAIN — Fast Deployment Helper
// ═══════════════════════════════════════════════════════════════════════════════

function tryPullChain(fast, slow, destination) {
  if (!hasActive(fast, MOVE) || fast.fatigue > 0) return false;
  if (getRange(slow, destination) <= 1) return false;

  if (getRange(fast, slow) <= 1) {
    fast.pull(slow);
    fast.moveTo(destination, pathOpts());
    slow.moveTo(fast);
    return true;
  }
  fast.moveTo(slow, pathOpts());
  return true;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  18 · DIAGNOSTICS & METRICS
// ═══════════════════════════════════════════════════════════════════════════════

const DIAG_INTERVAL = 100; // print compact log every N ticks

// Compact per-interval summary
function tickLog() {
  if (tick % DIAG_INTERVAL !== 0 && tick !== 1) return;

  const cpu = Math.round(getCpuTime() / 1e6); // ms
  diag.cpuSamples.push(cpu);

  const roles = {};
  for (const r of creepRoles.values()) roles[r] = (roles[r] || 0) + 1;

  // Tower energy status
  const towerStatus = myTowers.map(t => {
    const used = t.store ? t.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    const cap  = t.store ? t.store.getCapacity(RESOURCE_ENERGY)    : 0;
    return `${used}/${cap}`;
  }).join(' ');

  const myF  = allFlags.filter(f => f.my === true).length;
  const enF  = allFlags.filter(f => f.my === false).length;
  const neuF = allFlags.filter(f => f.my === undefined).length;
  const chargerCount = chargerToTower.size;

  console.log(
    `[T${tick}] CPU=${cpu}ms alive=${myCreeps.length} enemies=${enemies.length}` +
    ` flags(my=${myF} en=${enF} neu=${neuF})` +
    ` towers=[${towerStatus}] chargers=${chargerCount}` +
    ` roles=${JSON.stringify(roles)}`
  );
}

// Detect creeps that had no recorded action this tick
function detectAndLogIdle() {
  for (const creep of myCreeps) {
    if (creep.spawning) continue;
    if (!tickActions.has(creep.id)) {
      // behavior ran but didn’t call recordAction — count as idle
      const role = creepRoles.get(creep.id) || 'unknown';
      diag.idleTicks[creep.id] = (diag.idleTicks[creep.id] || 0) + 1;
      if (!diag.actionCounts[role]) {
        diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
      }
      diag.actionCounts[role].idle++;
      // Warn only once every 20 idle ticks so we don’t spam
      if (diag.idleTicks[creep.id] % 20 === 1) {
        console.log(`[IDLE T${tick}] creep ${creep.id.slice(-4)} role=${role} idleTicks=${diag.idleTicks[creep.id]}`);
      }
    }
  }
}

// Draw Visual overlays: role labels + HP bars
function drawVisuals() {
  const vis = new Visual(1, false);
  for (const creep of myCreeps) {
    if (creep.spawning) continue;
    const role = (creepRoles.get(creep.id) || '?')[0].toUpperCase();
    const hpRatio = creep.hits / creep.hitsMax;
    const color = hpRatio > 0.6 ? '#00ff88' : hpRatio > 0.3 ? '#ffaa00' : '#ff3333';
    vis.text(role, { x: creep.x, y: creep.y - 0.6 }, { font: '0.4', color: '#ffffff', opacity: 0.85 });
    // HP bar
    vis.rect({ x: creep.x - 0.5, y: creep.y + 0.4 }, 1, 0.15, { fill: '#333333', opacity: 0.7, stroke: undefined });
    vis.rect({ x: creep.x - 0.5, y: creep.y + 0.4 }, hpRatio, 0.15, { fill: color, opacity: 0.9, stroke: undefined });
  }
  // Container energy bars (tower supply depots)
  for (const cont of containers) {
    const energy = cont.store ? cont.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    const cap    = cont.store ? cont.store.getCapacity(RESOURCE_ENERGY) : 0;
    if (cap === 0) continue;
    const ratio = energy / cap;
    vis.rect({ x: cont.x - 0.5, y: cont.y + 0.4 }, ratio, 0.15, { fill: '#ffff00', opacity: 0.7, stroke: undefined });
    vis.text(`${energy}`, { x: cont.x, y: cont.y - 0.6 }, { font: '0.35', color: '#ffff88', opacity: 0.9 });
  }
}

// Full end-of-game diagnostic dump
function dumpEndGameDiag() {
  if (diag.gameDumped) return;
  diag.gameDumped = true;

  const myF  = allFlags.filter(f => f.my === true).length;
  const enF  = allFlags.filter(f => f.my === false).length;
  const neuF = allFlags.filter(f => f.my === undefined).length;

  const cpuAvg = diag.cpuSamples.length
    ? Math.round(diag.cpuSamples.reduce((a,b)=>a+b,0) / diag.cpuSamples.length)
    : 0;
  const cpuMax = diag.cpuSamples.length ? Math.max(...diag.cpuSamples) : 0;

  // Count total idle ticks
  const totalIdle = Object.values(diag.idleTicks).reduce((a,b)=>a+b,0);

  console.log('=== CTF END-OF-MATCH DIAGNOSTICS ===');
  console.log(`Tick: ${tick} | Survivors: ${myCreeps.length} | Flags: my=${myF} enemy=${enF} neutral=${neuF}`);
  console.log(`Start roster: ${JSON.stringify(diag.startRoster)}`);
  console.log(`Death events (${diag.deathEvents.length}): ` + diag.deathEvents.map(e => `T${e.tick}:${e.role}`).join(' | '));
  console.log(`Flag events (${diag.flagEvents.length}): ` + diag.flagEvents.map(e => `T${e.tick}:${e.type}`).join(' | '));
  console.log(`Total idle creep-ticks: ${totalIdle}`);
  console.log(`CPU samples: avg=${cpuAvg}ms max=${cpuMax}ms over ${diag.cpuSamples.length} intervals`);
  console.log('Action counts by role:');
  for (const [role, counts] of Object.entries(diag.actionCounts)) {
    console.log(`  ${role}: ${JSON.stringify(counts)}`);
  }
  console.log('=== END DIAGNOSTICS ===');
}
// ═══════════════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════════════
//  19 · MAIN LOOP — Per-Tick Orchestrator
// ═══════════════════════════════════════════════════════════════════════════════

export function loop() {
  // ─── SENSE ──────────────────────────────────────────────
  refreshWorldState();

  // ─── INITIALIZATION (first tick) ────────────────────────
  if (!initialized) {
    assignRoles();
    buildInfluenceMap();
    initialized = true;
  }

  // ─── PERIODIC ROLE RE-EVALUATION ────────────────────────
  if (tick > 1 && tick % ROLE_REEVAL_TICKS === 0) {
    reevaluateRoles();
  }

  // ─── REFRESH INFLUENCE MAP ─────────────────────────────
  getInfluenceMap();

  // ─── REFRESH TOWER LIST (captures change ownership) ────
  myTowers = allTowers.filter(t => t.my === true);

  // ─── TOWER ACTIONS ──────────────────────────────────────
  towerController();

  // ─── ASSIGN TOWER CHARGERS (one per hungry tower) ────────
  assignTowerChargers();

  // ─── COMMANDER LAYER — global objective assignment ────────
  commandLayer();

  // ─── CREEP ACTIONS ──────────────────────────────────────
  for (const creep of myCreeps) {
    if (creep.spawning) continue;
    executeTick(creep);
  }

  // ─── DIAGNOSTICS ────────────────────────────────────────
  detectAndLogIdle();
  tickLog();
  drawVisuals();

  // ─── END-OF-GAME DUMP ───────────────────────────────────
  const isLastTick = tick >= (arenaInfo.ticksLimit - 1);
  const allDead    = myCreeps.length === 0 && initialized;
  if (isLastTick || allDead) {
    dumpEndGameDiag();
  }
}