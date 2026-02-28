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
const ROLE_RUNNER    = 'runner';

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
const MOSQUITO_DETECT_RANGE    = 12;   // scan radius for local force balance
const MOSQUITO_FLEE_RANGE      = 5;    // start fleeing when enemies in r5
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
let currentTank        = null;   // creep ID of the designated tank (absorbs enemy focus)
let influenceMatrix    = null;
let lastInfluenceTick  = -Infinity;
let initialized        = false;

// ─── OBJECTIVE STICKINESS ─────────────────────────────────────────────────────
// Prevents oscillation: once committed to a flag, lock for STICKY_TICKS before
// re-evaluating. Resets on flag capture/loss or if objective disappears.
let stickyObjective    = null;   // the flag object
let stickySetTick      = -Infinity;
const STICKY_TICKS     = 40;

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
      // Release tank designation if this was the tank
      if (currentTank === id) currentTank = null;
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
    [ROLE_VANGUARD]: 0, [ROLE_RANGER]: 0, [ROLE_MEDIC]: 0, [ROLE_SENTINEL]: 0, [ROLE_RUNNER]: 0,
  };

  for (const creep of myCreeps) {
    const role = classifyCreep(creep);
    creepRoles.set(creep.id, role);
    counts[role]++;
  }

  // Designate 2 vanguards as dedicated flag RUNNERS (fastest first)
  const vanguardList = myCreeps
    .filter(c => creepRoles.get(c.id) === ROLE_VANGUARD)
    .sort((a, b) => countParts(b, MOVE) - countParts(a, MOVE));
  const numRunners = Math.min(2, vanguardList.length);
  for (let i = 0; i < numRunners; i++) {
    creepRoles.set(vanguardList[i].id, ROLE_RUNNER);
    counts[ROLE_VANGUARD]--;
    counts[ROLE_RUNNER]++;
  }

  // Snapshot initial roster for diagnostics
  if (!diag.startRoster) {
    diag.startRoster = { ...counts, total: myCreeps.length };
    for (const role of Object.keys(counts)) {
      diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
    }
    console.log(`[INIT T${tick}] Roster: ${JSON.stringify(diag.startRoster)}`);
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

  // Emergency: no vanguards but >1 runner → promote one runner back
  if (!counts[ROLE_VANGUARD] && (counts[ROLE_RUNNER] || 0) > 1) {
    const runnerList = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_RUNNER);
    if (runnerList.length > 0) creepRoles.set(runnerList[0].id, ROLE_VANGUARD);
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

/**
 * Aggressive pathing for melee engagements.
 * Omits enemy threat field so vanguards can actually close to melee range.
 * Still respects terrain costs (swamp/plain).
 */
function aggressivePathOpts() {
  return {
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
  if (role === ROLE_MEDIC) return false;
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
  const centroid = squadCentroid() || { x: 50, y: 50 };

  // ── Global focus target ──────────────────────────────────────────────────
  globalFocusTarget = enemies.length > 0 ? selectFocusTarget(centroid, enemies) : null;

  // ── Designate tank — picks healthiest vanguard for heal-ball formation ──
  designateTank();

  const uncaptured = [...neutralFlags, ...enemyFlags];
  const runners = myCreeps.filter(c =>
    creepRoles.get(c.id) === ROLE_RUNNER && !chargerToTower.has(c.id)
  );
  const mainArmy = myCreeps.filter(c => {
    const r = creepRoles.get(c.id);
    return r !== ROLE_RUNNER && !chargerToTower.has(c.id);
  });

  // ── Phase 1: Flag Rush ───────────────────────────────────────────────────
  // Runners rush flags independently. Main army stays TOGETHER and marches
  // to the nearest neutral flag as a deathball — never split the main army.
  if (tick <= PHASE_EXPAND_END && neutralFlags.length > 0) {
    assignRunnerTargets(runners);
    const nearestNeutral = neutralFlags.reduce((best, f) =>
      getRange(centroid, f) < getRange(centroid, best) ? f : best
    );
    for (const creep of mainArmy) {
      creepTargets.set(creep.id, nearestNeutral);
    }
    return;
  }

  // ── RUNNER TARGETS — always chase uncaptured flags ───────────────────────
  assignRunnerTargets(runners);

  // ── MAIN ARMY — hunt the largest enemy concentration ────────────────────
  const enemyCenter = findEnemyCentroid();
  if (enemyCenter && enemies.length > 0) {
    // All main army converges on enemy blob to destroy it
    for (const creep of mainArmy) {
      creepTargets.set(creep.id, enemyCenter);
    }
  } else {
    // No enemies — capture remaining flags
    const obj = uncaptured.length > 0
      ? uncaptured.reduce((best, f) =>
          getRange(centroid, f) < getRange(centroid, best) ? f : best)
      : myFlag;
    for (const creep of mainArmy) {
      creepTargets.set(creep.id, obj || myFlag);
    }
  }

  // ── FLAG DEFENSE INTERCEPTOR — anti-rush & anti-sneak ──────────────────
  const myOwnedFlags = allFlags.filter(f => f.my === true);
  for (const flag of myOwnedFlags) {
    const threatsNearFlag = findInRange(flag, enemies, 10);
    if (threatsNearFlag.length === 0) continue;
    const defendersNear = findInRange(flag, myCreeps, 5).filter(c =>
      !chargerToTower.has(c.id)
    );
    if (defendersNear.length > 0) continue;
    const interceptors = mainArmy.filter(c => {
      const r = creepRoles.get(c.id);
      return r === ROLE_VANGUARD || r === ROLE_RANGER;
    });
    if (interceptors.length === 0) continue;
    const closest = findClosestByRange(flag, interceptors);
    if (closest) creepTargets.set(closest.id, flag);
  }

  // ── STRAGGLER CONSOLIDATION ──────────────────────────────────────────────
  if (centroid) {
    for (const creep of mainArmy) {
      const distToCentroid = getRange(creep, centroid);
      if (distToCentroid > 15) {
        const nearbyEn = findInRange(creep, enemies, MOSQUITO_DETECT_RANGE);
        if (nearbyEn.length >= 3) {
          creepTargets.set(creep.id, centroid);
        }
      }
    }
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
    return r === ROLE_VANGUARD || r === ROLE_RANGER;
  });
  if (squad.length === 0) return null;
  const ax = Math.round(squad.reduce((s, c) => s + c.x, 0) / squad.length);
  const ay = Math.round(squad.reduce((s, c) => s + c.y, 0) / squad.length);
  return { x: ax, y: ay };
}

/**
 * Mosquito detection: is this creep in a genuinely-outnumbered small group
 * where it should kite toward allied mass instead of fighting?
 *
 * Conservative triggers — prevents the whole-army-fleeing cascade:
 * 1. NEVER triggers if this creep is part of the main army (≥60% of alive)
 * 2. NEVER triggers if we have global numerical dominance (≥1.5x)
 * 3. Only on genuine numeric disadvantage (enemies > allies * 1.3)
 */
function isMosquitoSituation(creep) {
  const localAllies  = findInRange(creep, myCreeps, MOSQUITO_DETECT_RANGE).length;
  const localEnemies = findInRange(creep, enemies, MOSQUITO_DETECT_RANGE).length;
  if (localEnemies < 3) return false;

  // Main army check: if ≥50% of our force is here, this IS the main fight — commit.
  // Prevents the whole-army-fleeing cascade where both halves of a split force flee.
  if (localAllies >= myCreeps.length * 0.5) return false;

  // Global dominance: if we outnumber enemy overall by 1.5x, always fight
  if (myCreeps.length >= enemies.length * 1.5) return false;

  // Trigger only on genuine disadvantage (50%+ more enemies locally)
  return localEnemies > localAllies * 1.5;
}

/**
 * Combat strength estimate for a group of creeps.
 * Used for opportunity aggression detection.
 */
function groupStrength(creeps) {
  let str = 0;
  for (const c of creeps) {
    str += countActive(c, ATTACK) * ATTACK_POWER;
    str += countActive(c, RANGED_ATTACK) * RANGED_ATTACK_POWER;
    str += countActive(c, HEAL) * HEAL_POWER;
  }
  return str;
}

/**
 * Designate the best tank: healthiest vanguard with most ATTACK+TOUGH parts.
 * The tank leads the heal-ball — all medics form behind it.
 * Called once per tick from commandLayer.
 */
function designateTank() {
  const vanguards = myCreeps.filter(c =>
    creepRoles.get(c.id) === ROLE_VANGUARD && !chargerToTower.has(c.id)
  );
  if (vanguards.length === 0) {
    currentTank = null;
    return;
  }
  // Prefer current tank if still alive and healthy (>40% HP)
  if (currentTank) {
    const ct = vanguards.find(c => c.id === currentTank);
    if (ct && ct.hits > ct.hitsMax * 0.40) return; // keep current
  }
  // Sort by HP ratio desc, then total body parts desc
  vanguards.sort((a, b) => {
    const ra = a.hits / a.hitsMax;
    const rb = b.hits / b.hitsMax;
    if (ra !== rb) return rb - ra;
    return b.body.length - a.body.length;
  });
  currentTank = vanguards[0].id;
}

/**
 * Compute the formation point for a medic: 3 tiles BEHIND the tank,
 * on the opposite side from the enemy threat centroid.
 * This is the core of the heal-ball micro.
 */
function getFormationPoint(tank) {
  // Enemy centroid (threat direction)
  const nearEnemies = findInRange(tank, enemies, 10);
  if (nearEnemies.length === 0) return null; // no enemies = no need for formation
  
  const ex = nearEnemies.reduce((s, e) => s + e.x, 0) / nearEnemies.length;
  const ey = nearEnemies.reduce((s, e) => s + e.y, 0) / nearEnemies.length;
  
  // Direction from enemies to tank (unit vector)
  const dx = tank.x - ex;
  const dy = tank.y - ey;
  const mag = Math.sqrt(dx * dx + dy * dy) || 1;
  
  // Formation point = 3 tiles behind tank (away from enemies)
  const fx = Math.round(tank.x + (dx / mag) * 3);
  const fy = Math.round(tank.y + (dy / mag) * 3);
  
  // Clamp to arena bounds
  return {
    x: Math.max(1, Math.min(98, fx)),
    y: Math.max(1, Math.min(98, fy)),
  };
}

/**
 * Find the centroid of the largest enemy cluster.
 * Used by main army to converge on the biggest enemy group.
 */
function findEnemyCentroid() {
  if (enemies.length === 0) return null;
  // Find the enemy with the most allies within r10 (cluster center)
  let bestCenter = enemies[0];
  let bestCount = 0;
  for (const enemy of enemies) {
    const count = findInRange(enemy, enemies, 10).length;
    if (count > bestCount) {
      bestCount = count;
      bestCenter = enemy;
    }
  }
  // Compute centroid of that cluster
  const cluster = findInRange(bestCenter, enemies, 10);
  const cx = Math.round(cluster.reduce((s, e) => s + e.x, 0) / cluster.length);
  const cy = Math.round(cluster.reduce((s, e) => s + e.y, 0) / cluster.length);
  return { x: cx, y: cy };
}

/**
 * Assign runner targets: distribute runners across uncaptured flags.
 * Prefers undefended flags (no enemies within 8 tiles).
 * If all flags captured, runners patrol owned flags to re-defend.
 */
function assignRunnerTargets(runners) {
  if (runners.length === 0) return;
  const uncaptured = [...neutralFlags, ...enemyFlags];

  if (uncaptured.length === 0) {
    // All flags captured — patrol our flags to quickly recapture if lost
    const myOwnedFlags = allFlags.filter(f => f.my === true);
    for (let i = 0; i < runners.length; i++) {
      const flag = myOwnedFlags[i % Math.max(1, myOwnedFlags.length)] || myFlag;
      if (flag) creepTargets.set(runners[i].id, flag);
    }
    return;
  }

  // Prefer undefended flags (no enemies within 8)
  const undefended = uncaptured.filter(f => findInRange(f, enemies, 8).length === 0);
  const pool = undefended.length > 0 ? undefended : uncaptured;

  // Distribute runners to different flags when possible
  const assigned = new Set();
  for (const runner of runners) {
    const sorted = pool.slice().sort((a, b) => getRange(runner, a) - getRange(runner, b));
    const target = sorted.find(f => !assigned.has(f.id)) || sorted[0];
    creepTargets.set(runner.id, target);
    if (target) assigned.add(target.id);
  }
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

  // RUNNER: defensive combat only — self-heal > ranged > melee
  if (role === ROLE_RUNNER) {
    if (hasActive(creep, HEAL) && creep.hits < creep.hitsMax) {
      creep.heal(creep); return 'heal';
    }
    if (hasActive(creep, RANGED_ATTACK)) {
      const inR3 = findInRange(creep, enemies, 3);
      if (inR3.length >= 3) { creep.rangedMassAttack(); return 'attack'; }
      if (inR3.length > 0) { creep.rangedAttack(inR3[0]); return 'attack'; }
    }
    if (hasActive(creep, ATTACK)) {
      const adj = findInRange(creep, enemies, 1);
      if (adj.length > 0) { creep.attack(adj[0]); return 'attack'; }
    }
    return null;
  }

  if (role === ROLE_MEDIC) {
    // Medics: healing always beats attacking.
    // Tank gets priority heals to sustain the heal-ball formation.
    if (hasActive(creep, HEAL)) {
      const damaged = myCreeps.filter(c => c.hits < c.hitsMax && c.id !== creep.id);
      const adjDmg  = findInRange(creep, damaged, 1);
      const nearDmg = findInRange(creep, damaged, 3);

      // Prefer tank if it's damaged and in range (concentrate heals on focal point)
      const tank = currentTank ? damaged.find(c => c.id === currentTank) : null;
      if (tank) {
        const tankDist = getRange(creep, tank);
        if (tankDist <= 1) { creep.heal(tank); return 'heal'; }
        if (tankDist <= 3) { creep.rangedHeal(tank); return 'heal'; }
      }

      // Heal by HP ratio (most critical first)
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
  const objective = creepTargets.get(creep.id);

  // ── P0: Emergency retreat ────────────────────────────────────────────────
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
    const medics = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
    if (medics.length > 0) {
      const nearest = findClosestByRange(creep, medics);
      if (nearest) { creep.moveTo(nearest, pathOpts()); return; }
    }
    if (myFlag) creep.moveTo(myFlag, pathOpts());
    return;
  }

  // ── RUNNER: dedicated flag capture — skip all combat/formation logic ─────
  if (role === ROLE_RUNNER) {
    if (bodyParts.some(b => b.x === creep.x && b.y === creep.y)) return;
    if (objective) {
      const nearEn = findInRange(creep, enemies, 6);
      creep.moveTo(objective, nearEn.length > 0 ? pathOpts() : aggressivePathOpts());
      return;
    }
    if (bodyParts.length > 0) {
      const bp = findClosestByRange(creep, bodyParts);
      if (bp && getRange(creep, bp) <= 8) { creep.moveTo(bp); return; }
    }
    return;
  }

  // ── P0.5: Soft pull-back — step toward nearest medic for heal ────────────
  if (shouldPullBack(creep)) {
    const medics = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_MEDIC);
    if (medics.length > 0) {
      const nearest = findClosestByRange(creep, medics);
      if (nearest && getRange(creep, nearest) > 1) {
        creep.moveTo(nearest, pathOpts()); return;
      }
    }
    // No medics or already adjacent — keep fighting
  }

  // ── P1: Body part on same tile — stay to auto-collect ─────────────────
  if (bodyParts.some(b => b.x === creep.x && b.y === creep.y)) return;

  // ── P1.5: MOSQUITO KITE-BACK — sustain & kite toward allied mass ─────
  // Genuinely outnumbered small group? Walk toward allies or tower cover.
  // Conservative: main army and dominant forces NEVER trigger this.
  //
  // CRITICAL: NO searchPath(flee) here. flee=true + influence map penalties
  // create conflicting forces that trap creeps in corners/swamps/dead-ends.
  // Instead, ALWAYS moveTo(safePoint) — the pathfinder routes AROUND enemy
  // clusters while heading toward the real destination (allied centroid).
  // This inherently kites away from the deathball because allies are on the
  // opposite side of the map.
  if (isMosquitoSituation(creep)) {
    const farAllies = myCreeps.filter(c =>
      c.id !== creep.id && getRange(creep, c) > MOSQUITO_DETECT_RANGE
    );

    let safePoint = null;
    if (farAllies.length >= 1) {
      const cx = Math.round(farAllies.reduce((s, c) => s + c.x, 0) / farAllies.length);
      const cy = Math.round(farAllies.reduce((s, c) => s + c.y, 0) / farAllies.length);
      safePoint = { x: cx, y: cy };
    } else {
      // No far allies — universally outnumbered. Fall back to tower or own flag.
      const activeTower = myTowers.find(t =>
        t.store && t.store.getUsedCapacity(RESOURCE_ENERGY) > 0
      );
      safePoint = activeTower || myFlag;
    }

    if (safePoint) {
      creep.moveTo(safePoint, pathOpts());
      return;
    }
  }

  // ── P1.7: OPPORTUNITY AGGRESSION — pursue weak enemy groups ───────────
  // Only RANGERS chase scouts. Vanguards NEVER chase — they hold the screen.
  if (role === ROLE_RANGER) {
    const localAllies  = findInRange(creep, myCreeps, 8);
    const localEnemies = findInRange(creep, enemies, 10);
    if (localEnemies.length > 0 && localEnemies.length <= 3 &&
        groupStrength(localAllies) > groupStrength(localEnemies) * 2) {
      const target = selectFocusTarget(creep, localEnemies);
      if (target) {
        creep.moveTo(target, pathOpts());
        return;
      }
    }
  }

  // ── P2: FLAG CAPTURE — go capture nearby uncaptured flag ──────────────
  // Only when not in combat range. Vanguards suppress if ANY enemy in r6
  // (their engagement range) to avoid flag-detours during combat.
  // Rangers/Medics suppress at r3 (they can kite/heal near flags).
  {
    const suppressR = role === ROLE_VANGUARD ? 8 : 3;
    if (findInRange(creep, enemies, suppressR).length === 0) {
      const capRadius = role === ROLE_MEDIC ? 3 : 8;
      const uncapturedFlags = [...neutralFlags, ...enemyFlags];
      if (uncapturedFlags.length > 0) {
        const nearest = findClosestByRange(creep, uncapturedFlags);
        if (nearest && getRange(creep, nearest) <= capRadius) {
          creep.moveTo(nearest); return;
        }
      }
    }
  }

  // ── P3: COMBAT — role-specific ────────────────────────────────────────
  if (role === ROLE_VANGUARD) {
    // === ALWAYS ENGAGE ===
    // Vanguards ALWAYS close to melee — they are the frontline.
    // Medics follow THEM (M4 follows at r1). Vanguards NEVER wait for medics.
    // doCombatAction handles the ATTACK action at r1.

    const inR1 = findInRange(creep, enemies, 1);
    if (inR1.length > 0) return; // Melee contact — HOLD, doCombatAction attacks

    const nearEn = findInRange(creep, enemies, 8);
    if (nearEn.length > 0) {
      const target = (globalFocusTarget && nearEn.some(e => e.id === globalFocusTarget.id))
        ? globalFocusTarget
        : findClosestByRange(creep, nearEn);
      if (target) { creep.moveTo(target, aggressivePathOpts()); return; }
    }
    // No enemies in r8 — advance to objective aggressively
    if (objective) { creep.moveTo(objective, aggressivePathOpts()); return; }
  }

  if (role === ROLE_RANGER) {
    // Rangers: DPS dealers. Kite at r3, stay behind vanguard screen.
    const inR2 = findInRange(creep, enemies, 2);
    const inR3 = findInRange(creep, enemies, 3);
    const inR6 = findInRange(creep, enemies, 6);
    const vanguards = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_VANGUARD);

    if (inR2.length > 0) {
      // Too close — step toward vanguard screen for body-block cover
      const nearV = vanguards.length > 0 ? findClosestByRange(creep, vanguards) : null;
      if (nearV && getRange(creep, nearV) > 1) {
        creep.moveTo(nearV, pathOpts()); return;
      }
      // No vanguards or already adjacent — flee toward squad centroid
      const safePt = squadCentroid() || myFlag;
      if (safePt) { creep.moveTo(safePt, pathOpts()); return; }
    }
    if (inR3.length > 0) return; // Perfect kite range — hold and shoot
    if (inR6.length > 0) {
      // Approach to r3 but stay behind vanguard screen
      const nearestVan = vanguards.length > 0 ? findClosestByRange(creep, vanguards) : null;
      const t = selectFocusTarget(creep, inR6);
      if (t) {
        if (nearestVan) {
          const vanDistToEnemy = getRange(nearestVan, t);
          const myDistToEnemy = getRange(creep, t);
          if (myDistToEnemy > vanDistToEnemy) {
            creep.moveTo(t, pathOpts()); return;
          }
          creep.moveTo(nearestVan, pathOpts()); return;
        }
        creep.moveTo(t, pathOpts()); return;
      }
    }
  }

  if (role === ROLE_MEDIC) {
    // Medics: tight heal support. Follow vanguards at r1.
    // When allies are in combat, use aggressivePathOpts to NOT detour around
    // the enemy threat field (which would leave vanguards to die unsupported).
    const allies = myCreeps.filter(c => c.id !== creep.id);
    const vanguards = allies.filter(c => creepRoles.get(c.id) === ROLE_VANGUARD);
    const alliesInCombat = allies.some(c => findInRange(c, enemies, 3).length > 0);
    const moveOpts = alliesInCombat ? aggressivePathOpts() : pathOpts();

    // M0: Critical ally (<50% HP) — rush to r1
    const critical = allies.filter(c => c.hits < c.hitsMax * 0.50);
    if (critical.length > 0) {
      const worst = critical.reduce((b, c) =>
        (c.hits / c.hitsMax) < (b.hits / b.hitsMax) ? c : b
      );
      if (getRange(creep, worst) > 1) { creep.moveTo(worst, aggressivePathOpts()); return; }
      return;
    }

    // M1: Damaged ally within r3 — HOLD (doCombatAction handles rangedHeal)
    const dmgInR3 = allies.filter(c => c.hits < c.hitsMax * 0.90 && getRange(creep, c) <= 3);
    if (dmgInR3.length > 0) return;

    // M2: Damaged ally beyond r3 — approach
    const damaged = allies.filter(c => c.hits < c.hitsMax * 0.90);
    if (damaged.length > 0) {
      const worst = damaged.reduce((b, c) =>
        (c.hits / c.hitsMax) < (b.hits / b.hitsMax) ? c : b
      );
      creep.moveTo(worst, moveOpts); return;
    }

    // M3: Follow nearest vanguard at r1 — TIGHT formation
    if (vanguards.length > 0) {
      const nearest = findClosestByRange(creep, vanguards);
      if (nearest && getRange(creep, nearest) > 1) {
        creep.moveTo(nearest, moveOpts); return;
      }
      return; // At r1 of vanguard — hold and heal
    }

    // No vanguards — follow nearest combat ally at r2
    const combatAllies = allies.filter(c => creepRoles.get(c.id) === ROLE_RANGER);
    if (combatAllies.length > 0) {
      const nearest = findClosestByRange(creep, combatAllies);
      if (nearest && getRange(creep, nearest) > 2) {
        creep.moveTo(nearest, moveOpts); return;
      }
    }
    // Fall through to P4
  }

  // ── P4: Advance to objective ─────────────────────────────────────────
  // Vanguards use aggressive pathing (they ARE the frontline).
  // Others use influence-aware pathing for safety.
  if (objective) {
    const opts = (role === ROLE_VANGUARD) ? aggressivePathOpts() : pathOpts();
    creep.moveTo(objective, opts);
    return;
  }

  // ── P5: Collect body parts (idle behavior, lowest priority) ──────────
  if (bodyParts.length > 0) {
    const nearest = findClosestByRange(creep, bodyParts);
    if (nearest && getRange(creep, nearest) <= BODYPART_DEVIATE_RANGE) {
      creep.moveTo(nearest); return;
    }
  }
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
  const mosquitoCount = myCreeps.filter(c => isMosquitoSituation(c)).length;

  // Runner target info
  const runnerInfo = myCreeps
    .filter(c => creepRoles.get(c.id) === ROLE_RUNNER)
    .map(c => {
      const t = creepTargets.get(c.id);
      return t ? `(${t.x},${t.y})` : '(?)';
    }).join(' ');

  // Enemy centroid
  const ec = findEnemyCentroid();
  const ecStr = ec ? `(${ec.x},${ec.y})` : 'none';

  console.log(
    `[T${tick}] CPU=${cpu}ms alive=${myCreeps.length} enemies=${enemies.length}` +
    ` flags(my=${myF} en=${enF} neu=${neuF})` +
    ` towers=[${towerStatus}] chargers=${chargerCount}` +
    ` mosquito=${mosquitoCount}` +
    ` runners=[${runnerInfo}] enemyCenter=${ecStr}` +
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
    const roleId = creepRoles.get(creep.id) || '?';
    const label = roleId === ROLE_RUNNER ? 'F' : roleId[0].toUpperCase();
    const hpRatio = creep.hits / creep.hitsMax;
    const color = hpRatio > 0.6 ? '#00ff88' : hpRatio > 0.3 ? '#ffaa00' : '#ff3333';
    vis.text(label, { x: creep.x, y: creep.y - 0.6 }, { font: '0.4', color: '#ffffff', opacity: 0.85 });
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
  console.log(`Tick: ${tick} | Survivors: ${myCreeps.length} | Enemies: ${enemies.length}`);
  console.log(`Flags: my=${myF} enemy=${enF} neutral=${neuF}`);
  console.log(`Start roster: ${JSON.stringify(diag.startRoster)}`);
  console.log(`Death events (${diag.deathEvents.length}): ` + diag.deathEvents.map(e => `T${e.tick}:${e.role}`).join(' | '));
  console.log(`Flag events (${diag.flagEvents.length}): ` + diag.flagEvents.map(e => `T${e.tick}:${e.type}`).join(' | '));
  console.log(`Total idle creep-ticks: ${totalIdle}`);
  console.log(`CPU samples: avg=${cpuAvg}ms max=${cpuMax}ms over ${diag.cpuSamples.length} intervals`);
  console.log('Action counts by role:');
  for (const [role, counts] of Object.entries(diag.actionCounts)) {
    const total = Object.values(counts).reduce((a, b) => a + b, 0);
    const atkPct = total > 0 ? ((counts.attack / total) * 100).toFixed(1) : '0.0';
    console.log(`  ${role}: ${JSON.stringify(counts)} (atk%=${atkPct})`);
  }
  // Per-survivor summary
  console.log('Survivors:');
  for (const creep of myCreeps) {
    const r = creepRoles.get(creep.id) || '?';
    const hpPct = ((creep.hits / creep.hitsMax) * 100).toFixed(0);
    console.log(`  ${r} hp=${hpPct}% pos=(${creep.x},${creep.y})`);
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