# ric3 fork

README is linked to AGENTS.md 'cause ric3 is so nuanced it's best to understand
before **using** it. The goal is to make the solver architecture, the useful
command-line knobs, and the local naming conventions explicit enough that one
at least vaguely knows what it is doing.

The current checkout is a Rust hardware model checker for AIGER and BTOR/BTOR2
inputs. The bit-level path is the main path. RLive and the word-level engines
exist, but are immature.

## Repository Map

- `src/main.rs`: CLI entry point. Defines `check` and `preprocess`.
- `src/config.rs`: engine and preprocessing Clap configuration.
- `src/ic3/`: bit-level IC3 engine and all IC3 tricks.
- `src/gipsat/`: custom incremental SAT solver used by IC3 and preprocessing.
- `src/cadical/`: concrete CaDiCaL wrapper used by BMC, K-induction, local abstraction, simplification, and certification.
- `src/kissat/`: concrete Kissat wrapper used by the non-incremental Kissat BMC path.
- `src/bmc.rs`: bit-level bounded model checking.
- `src/kind.rs`: bit-level K-induction.
- `src/transys/`: bit-level transition-system representation, preprocessing, unrolling, witness/proof restore.
- `src/frontend/aig`, `src/frontend/btor`: parsers/frontends that build `Transys`.
- `src/logic/`: low-level `Var`, `Lit`, CNF/DAG-CNF, vector, bitset, and map utilities.
- `src/rlive/`, `src/wlbmc.rs`, `src/wlkind.rs`, `src/wltransys/`: available but not the normal path for this guide.
- `tools/run-ric3.py`: benchmark & portfolio runner.
- `ric3` rust binary provides primitive solver commands, not proof orchestration. Portfolio runs are script-driven through `./tools`, especially `tools/run-ric3.py`.

## Command Shape

Primary command:

```sh
ric3 check <model.aig|model.aag|model.btor|model.btor2> [preproc flags] <engine> [engine flags]
# Examples:
ric3 check model.aig ic3
ric3 check model.aig --no-scorr --no-frts ic3 --no-ctg --no-drop-po
ric3 check model.aig ic3 --ctg-max 5 --ctg-limit 15 --no-drop-po
ric3 check model.aig ic3 --inn --ctp
ric3 check model.aig bmc --kissat --step 65
ric3 check model.aig kind --simple-path
```

Default-on features use `--no-*` to disable them. Default-off features
such as `--inn` and `--guard-domain` use ordinary presence switches.
Useful top-level `check` flags:
- `--cert <path>`: write a safety or counterexample certificate.
- `--certify`: ask the frontend to certify the certificate with the external certifier path flow.
- `--witness`: print the unsafe witness.
- `--prop <id>`: preserve/check one property by index during preprocessing. If omitted and there are multiple bad properties, bit-level engines compress them with an OR at different points.

Useful `preprocess` command:
```sh
ric3 preprocess <model> --preproc-file <file>
ric3 check <model> --preproc-file <file> ic3
```

`--preproc-file` exports the preprocessed bit-level `Transys`, its restore
metadata, and the elapsed preprocessing time; without it, `preprocess` discards
the result. On `check`, a readable, valid file skips preprocessing; a missing or
invalid file falls back to normal preprocessing. `--fake-preproc-wait` sleeps for
the recorded preprocessing time after loading, useful for fair benchmark accounting.
The loaded model is used as saved: preprocessing switches and `--prop` are not
reapplied. The caller must ensure the cache matches the selected property and
engine mode (including `--local-proof`); loading an incompatible cache has
undefined behavior.

## Preprocessing

`Transys::preproc` has three phases: quick greedy/trivial simplification,
sequential latch sweep (`scorr`), and combinational sweep (`frts`). Trivial
simplification always runs; there is no `--preproc` switch. Disable the expensive phases with
`--no-scorr` and/or `--no-frts`. A successfully loaded `--preproc-file` skips
all three phases.

### Phase 1: quick greedy/trivial rewrites

Implemented in `src/transys/simp.rs` through `Transys::simplify`. This phase performs:
- COI refinement from bad properties, constraints, justice signals, latches, initial values, and DAG dependencies.
- DAG-CNF simplification with frozen variables for semantically important objects.
- Constant simplification, bounded variable elimination, subsumption/self-subsumption, and clause cleanup through `DagCnfSimplify`.
- Constraint cleanup and deduplication.
- Variable rearrangement so active variables are dense and restore mappings remain correct.
This pass is always enabled. It is cheap relative to scorr/frts/IC3 and removes
irrelevant cones before the bit-level engine starts.

### Phase 2: `scorr` `src/transys/scorr.rs`

Enabled by default; `--no-scorr` disables it. `--scorr-tl <seconds>`, default
200. `scorr` is sequential correlation. It tries to prove that latches are
equivalent or inverted-equivalent over reachable behavior, then replaces one
with the other. The implementation:
- Generates initial-state simulation signatures.
- Generates reachable-transition simulation signatures.
- Buckets latch literals by equal or inverted signatures.
- Uses GipSAT to check both initial consistency and inductive preservation.
- Replaces proven correlated latches and reruns simplification.

### Phase 3: `frts` `src/transys/frts.rs`

Enabled by default; `--no-frts` disables it. `--frts-tl <seconds>`, default 1000.
`frts` is functional reduction for the transition-system DAG. It starts with
random simulation over the DAG, proposes equivalent or inverted-equivalent
internal variables, and then validates those candidates with GipSAT. Proven
equalities are added to the SAT solver, accumulated in a replacement map, and
periodically applied to the transition system.

Note that  there are tiny runs where `scorr/frts` time dominates.

## Bit-Level IC3 `src/ic3`

```sh
ric3 check <model> ic3 [flags]
```

IC3 is the main engine. It maintains frames of lemmas over the transition system, repeatedly finds bad states at the frontier, blocks proof obligations by relative induction, generalizes blocked cubes into lemmas, pushes lemmas forward, and proves safety when a frame becomes empty or an inductive invariant is formed.

### Main loop, as implemented

Initialization is in `IC3::new` (`src/ic3/mod.rs`); the main loop is in
`IC3::check` (`src/ic3/mainloop.rs`):

1. `IC3::new` removes gate initializations, configures INN/predicate-property mode, checks the predicate-property base case, and constructs frame 0 with initial-state lemmas.
2. `check` pops queued obligations at the frontier, ordered by frame, trace depth, and cube size.
3. If an obligation intersects the initial condition at frame 0, IC3 returns unsafe. With local abstraction enabled, it first validates/refines the abstract witness with BMC.
4. Otherwise, query the previous frame solver using next-state cube assumptions (`dcs_solve_nocst`).
5. If SAT, obtain a predecessor with `get_pred`, enqueue it one frame earlier, and requeue the current obligation.
6. If UNSAT, extract an `inductive_core`, minimize it with MIC/CTG, push it with `push_lemma`, then add the lemma to the frames.
7. Once queued obligations are handled, `get_bad` searches the frontier and enqueues a lifted predecessor/state cube if one exists.
8. If no bad state remains, clone the infinity solver to extend the frontier and call `propagate`. An empty frame proves safety.
9. `propagate_to_inf` tries to move frontier lemmas into the infinity frame.

The implementation is not a toy PDR. Most of the performance is in the choices made inside MIC, propagation, predecessor lifting, and SAT-local domains.

### IC3 CLI flags

- `--rseed <u64>`: random seed for cube shuffling and related randomized decisions. Default 0.
- `--time-limit <seconds>`: IC3 time limit. Default `u64::MAX`.
- `--no-ctg`: disable counterexample-to-generalization, which is enabled by default.
- `--ctg-max <usize>`: maximum CTG retries before shrinking by the current SAT model. Default 3.
- `--ctg-limit <usize>`: recursive blocking budget for CTG. Default 1.
- `--dynamic`: simple activity-based dynamic EXCTG/CTG parameter selection. Default false.
- `--mab`: LinUCB multi-armed-bandit parameter selection. Default false.
- `--mab-alpha <f64>`: LinUCB exploration parameter. Default 1.0.
- `--mab-lambda <f64>`: LinUCB regularization parameter. Default 0.1.
- `--ctp`: counterexample-to-propagation. Default false.
- `--inn`: internal-signal IC3. Default false.
- `--guard-domain`: singleton least-seen guarded latch domains.
- `--abs-cst`: local abstraction of constraints. Default false.
- `--abs-trans`: local abstraction of transition connections. Default false.
- `--no-drop-po`: disable dropping over-active proof obligations, enabled by default.
- `--no-parent-lemma`: disable parent lemma guidance during MIC, enabled by default.
- `--pred-prop`: predicate-property mode. Default false.
- `--local-proof <usize>`: local proof/property selection path. Commented as buggy; avoid unless explicitly working on it.

Important incompatibilities enforced by `IC3::new`:
- `--dynamic` and `--mab` cannot both be enabled.
- `--dynamic` and `--mab` require `--no-drop-po` because dropping is enabled by default.
- `--inn` cannot be combined with `--abs-cst`, `--abs-trans`, or `--guard-domain`.

### Counterexample to Generalization, CTG `src/ic3/mic.rs`

```sh
--no-ctg # disable CTG
--ctg-max <n>
--ctg-limit <n>
# default: CTG enabled
--ctg-max=3 --ctg-limit=1
# useful recipes:
ric3 check model.btor ic3 --no-ctg --no-drop-po # disable
ric3 check model.btor ic3 --ctg-max 5 --ctg-limit 15 --no-drop-po # aggressive
```

CTG is used inside MIC, not as a separate outer loop. When MIC tries to drop a literal from a blocked cube, the resulting smaller cube may fail the relative-induction query. The SAT model for that failure is a counterexample to the proposed generalization. If that counterexample is itself blockable at a lower frame, the literal drop can still be accepted after recursively blocking the CTG.  
Implementation details:

- MIC is represented by `DropVarParameter { limit, max, level }`.
- Default CTG maps to `DropVarParameter::new(ctg_limit, ctg_max, 1)`.
- `level == 0` uses plain `down`: test the dropped cube directly, shrink by the SAT model/core, and remember failed counterexamples.
- `level > 0` uses `ctg_down`: if a dropped cube is not blocked, get the predecessor/model and try `trivial_block(frame - 1, model, ..., parameter.sub_level())`.
- `ctg-max` limits consecutive CTG recursive attempts before accepting the current SAT model as evidence for keeping literals.
- `ctg-limit` is the budget passed to recursive `trivial_block_rec`.

Good cases:
- Safe instances where many failed literal drops are caused by states that are reachable in the SAT abstraction but blockable in earlier frames.
- Proofs needing short lemmas; CTG spends SAT work to avoid bloated clauses.
- Runs with `--no-drop-po`, where the solver is allowed to keep working through hard obligations rather than dropping them.

Bad cases:
- Shallow unsafe instances. CTG may spend time polishing lemmas when BMC-like search would already find the bug.
- Instances with genuinely reachable CTGs. Recursive blocking fails and the extra calls are pure overhead.
- Very small models where default IC3 already finds an invariant quickly.

### Extended CTG and dynamic EXCTG generation `src/ic3/mab.rs`

There is no separate `--exctg` flag. Extended CTG behavior is expressed by
choosing stronger `DropVarParameter` settings, either statically with
`--ctg-max/--ctg-limit` or dynamically with `--dynamic` or `--mab`. Ex:
```sh
ric3 check model.aig ic3 --dynamic --no-drop-po # simple dynamic mode
ric3 check model.aig ic3 --mab --no-drop-po # MAB mode
ric3 check model.aig ic3 --mab --mab-alpha 0.7 --mab-lambda 0.1 --no-drop-po
```

the simple dynamic mode does not learn. It computes a CTG parameter from proof-obligation activity along the successor chain:
- Low branch activity: use no CTG or almost no CTG.
- Medium activity: use small CTG.
- High activity: grow the CTG recursive budget and allow up to 5 CTGs.

The MAB mode uses LinUCB to choose among several CTG/generalization arms. The
context vector is: `[relative level, relative cube size, push potential,
relative depth, frame saturation, activity, bias]`. The arms include:
- Dynamic balanced.
- Dynamic aggressive.
- Dynamic conservative.
- Fixed no-CTG.
- Fixed conservative CTG.
- Fixed balanced CTG.
- Fixed aggressive/deep CTG.

The reward favors smaller generalized cubes, successful pushes to later frames, frontier pushes, and single-literal lemmas. It penalizes unpushable clauses and over-generalization that shrinks hard but fails to push.

Good cases:
- Long-running safe instances with enough obligations for learning to pay off.
- Heterogeneous benchmark sets where a single CTG setting is not robust.

Bad cases:
- Short runs, shallow bugs, and tiny models.

### Counterexample to Propagation, CTP `src/ic3/propagate.rs`

CLI: `--ctp` Default false.

CTP is the propagation-side counterpart to CTG. During propagation, when a lemma from frame `i` does not push to frame `i + 1`, the failed SAT query yields a counterexample to propagation. If that counterexample can itself be blocked at frame `i`, IC3 learns a new lemma and retries propagation.

Implementation details:
- Propagation tries each lemma normally first.
- If propagation fails and `--ctp` is disabled, it stops on that lemma.
- If `--ctp` is enabled, it gets the predecessor/model for the failed propagation.
- If the CTP state is not initial and is inductive at the previous frame, IC3 extracts a core, runs MIC with default/no CTG parameters, adds the lemma, and retries.
- The loop tries up to 3 CTP rounds per lemma.

Good cases:
- Proofs where blocking succeeds but propagation stalls on a small number of missing lemmas.
- Internal-signal runs. The benchmark runner has a practical recipe `--inn --ctp`.
- Cases where frontier lemmas are almost inductive but need local strengthening.

Bad cases:
- Runs where propagation is not the bottleneck.
- Large frames with many lemmas, where failed propagation already costs enough.

### Internal Signal IC3 `src/ic3/mod.rs`, `src/transys/unroll.rs`

CLI: `--inn` Default false.

Internal-signal IC3 treats selected combinational variables as latch-like state
variables. `IC3::new` performs one unroll and calls `internal_signals()` when
`--inn` is enabled. Predicate-property mode reuses `internal_signals()` and
retains the next-state predicate mapping. Why it helps:
- Standard IC3 lemmas are over latches. On bit-blasted circuits, the latch state can be too coarse.
- Internal combinational signals can expose useful cut points in the transition relation.
- Lemmas over these cut points can be shorter or easier to propagate.

Good cases:
- Deep combinational logic between flops.
- Designs where the useful invariant is naturally about decoded/control/internal wires.
- Bit-level HWMCC-style instances where state-only lemmas are weak.

Bad cases:
- Models where adding internal signals explodes the state space more than it helps.

### Local Abstraction `src/ic3/localabs.rs`

CLI: `--abs-cst --abs-trans` Default both false.

Local abstraction is used to validate and refine potential counterexamples in an abstracted transition system. It starts with a refinement set containing constants and bad variables. Depending on flags, constraints and transition connections are made optional with activation variables.

Modes:
- `--abs-cst`: constraints are abstractable. The abstraction may omit constraints until a spurious witness forces refinement.
- `--abs-trans`: latch transition connections are abstractable. Optional variables guard the equality between the next expression and the next-frame latch.
- `--abs-cst --abs-trans`: abstract both constraints and transition connections.

When an obligation reaches the initial frame under abstraction:
1. IC3 re-adds the obligation and runs abstract BMC to the witness depth.
2. If the abstract witness is not real, the unsat core identifies optional variables to refine.
3. Those variables are permanently enabled by clauses.
4. IC3 clears obligations and proof-obligation links in frames, then continues.
5. If witness checking passes, IC3 returns unsafe and can emit the concrete witness.

Good cases:
- Large transition systems where only a small part matters to the current bug/proof path.
- Unsafe or near-unsafe instances where abstract witnesses quickly identify the relevant cone.
- Constraint-heavy encodings where many constraints are irrelevant most of the time.

Bad cases:
- Proofs needing most of the design from the start.
- Where paths to proof trace are narrow. **`--abs*` are the most RNG sensitive switches across `ric3`**.

### Drop Proof Obligation `src/ic3/mainloop.rs`

Enabled by default; `--no-drop-po` disables it.

Each proof obligation has an activity score. It increments when the obligation is revisited and decays when the obligation is pushed to later frames. With dropping enabled and activity above 20, the main loop drops the obligation instead of continuing to chase that branch.

Good cases:
- Portfolio-style runs where escaping a pathological obligation chain is worth it.
- Instances with many alternative bad states, where the frontier can rediscover useful work later.

Bad cases:
- Cases where a dropped branch is exactly the one that would have yielded the decisive lemma.

### Predicate Property `src/ic3/predprop.rs`

CLI: `--pred-prop` Default false.

Predicate-property mode changes how IC3 asks for frontier bad states. It builds a secondary transition system over predecessor/property predicates and uses that solver to produce bad predecessors, then lifts them back into state/input cubes.

Implementation notes:
- `PredProp::new` compiles one-step behavior, or the internal-signal variant when `--inn` is enabled.
- It adds the original bad condition as a constraint in the predicate-property system.
- `IC3::new` first checks for a depth-0 counterexample.
- If base is safe, the main transition system gets `!bad` as a constraint and IC3 searches predecessors instead of direct bad states.
- When frames extend, the predicate-property solver is rebuilt with infinity-frame lemmas.

Good cases:
- Cases where direct bad-state queries are too broad and predecessor queries are more informative.
- Designs with bad properties that are easy to hit syntactically but hard to lift well.
- Some multi-property/local-property experiments.

Bad cases:
- Simple bad states where direct `get_bad` is already cheap.

### Finding Parent Lemma `src/ic3/mic.rs`, `src/ic3/frame.rs`

Enabled by default; `--no-parent-lemma` disables it.

This is the "generalize toward look-alike lemmas in parent frames" trick.
During MIC, if the previous frame contains a lemma that subsumes the current
cube, IC3 changes the drop order so literals outside that parent shape are
tried first. The result is a generalized lemma that tends to resemble the
parent lemma. Why it helps:
- IC3 often learns families of similar lemmas across adjacent frames.
- Generalizing toward a parent can produce clauses that push better.
- It complements CTP: CTP learns missing propagation-side lemmas, while parent-lemma guidance shapes blocking-side MIC toward lemmas that already have a propagation history.

Good cases:
- Proofs with repeated, layered lemma families.
- Runs with many similar obligations across frames.
- Default safe-proof workloads.

Bad cases:
- Rare cases where parent resemblance over-biases MIC away from a smaller unrelated lemma.

### Miscellaneous IC3 Notes

- `Activity` is used to sort literals for blocking/MIC and to score obligations for dynamic CTG.
- `Poq` (Proof Obligation Queue) prioritizes higher frame, shallower trace depth, then smaller cube.
- `Frame::trivial_contained` avoids adding or reblocking cubes already subsumed by known lemmas.
- `add_lemma` removes subsumed lemmas in earlier frames and can detect an empty frame as proof.
- `propagate_to_inf` tries to move frontier lemmas to an infinity frame and can recursively prove the CTP needed to do so.
- `local-proof` is present but marked buggy in source.

## BMC `src/bmc.rs`

BMC removes transition-system dependencies into a no-dependency CNF form, turns
constraints into clauses, simplifies, then incrementally unrolls the transition
relation and asks whether any bad property holds at each checked depth. Current flags:
- `--start <usize>`: first bound. Default 0.
- `--end <usize>`: maximum bound/depth. Default `usize::MAX`.
- `--step <u32>`: check every Nth bound. Default 1.
- `--rseed <u64>`: seed for SAT solver randomization. Default 0.
- `--kissat`: use Kissat instead of CaDiCaL. Default false.
- `--dyn-step`: choose a step from model size, roughly `10_000_000 / (max_var + num_clauses)`.

Practical guidance:
- `--kissat` is often the better BMC choice for large step raw bug hunting.
- `--step` and `--dyn-step` are benchmark throughput knobs. They can skip the first failing depth if set too coarsely, although the engine reports the depth it actually checked.
- Usually keep `--end` unset, i.e., loop till counterexample found.
- BMC outperforms IC3 in *most* unsafe cases.
- IC3 can generalize across states and may outperform BMC on deep unsafe cases.

## K-Induction `src/kind.rs`

K-induction uses the same no-dependency unrolling style as BMC, with a base
check and an inductive step. For each `k`, unless `--skip-bmc` is set, it first
checks whether a bad state exists at depth `k - 1`. Then it asserts bad states
false for previous frames and asks whether `bad@k` is impossible. If
impossible, the property is K-inductive and safe. Current flags:
- `--end <usize>`: maximum bound. Default `usize::MAX`.
- `--simple-path`: add simple-path constraints. Default false.
- `--skip-bmc`: skip the base BMC query. Default false.
- `--local-proof <usize>`: present but immature

Practical guidance:
- `--simple-path` adds pairwise disequality constraints between the new state and all earlier states using XOR helper variables. This can make non-inductive properties inductive by ruling out loops.
- Simple path is expensive: roughly O(k^2 * number_of_latches) extra structure over time.
- `--skip-bmc` is only for special experiments. Normally keep the base check.
- Solves some cases unsolvable by IC3, though generally underperforms it.

## GipSAT `src/gipsat/`

GipSAT is the custom SAT solver powering IC3, `scorr`, and `frts`. It is
designed for many small, related transition-system queries rather than
standalone SAT competition use.  `DagCnfSolver`, CaDiCaL, and Kissat are
independent solvers used at unrelated occasions. `DagCnfSolver::dcs_solve`
takes mutable assumptions, temporary constraints, an extra local domain, and
a restart limit. `dcs_solve_nocst` is the convenient no-constraint wrapper.
For `dcs_solve` with constraints, callers sort each clause and reserve its last
slot for an activation literal, and reserve assumption slot 0 for activation.

For agent navigation, grep the full concrete names. These names are
intentionally noise-free across the tree and lead directly to each concrete
implementation and all of its call sites:
- GipSAT: `dcs_solve`, `dcs_satval`, and `dcs_varsatval`.
- CaDiCaL: `cad_solve` and `cad_satval`.
- Kissat: `ksat_solve` and `ksat_satval`.
- Bitwuzla: `bzla_solve` and `bzla_satval`.

Core pieces:
- `DagCnfSolver`: incremental SAT solver over `DagCnf`.
- `ClauseDB`: stores transition clauses, IC3 lemmas, learnt clauses, and temporary clauses separately.
- `Watchers`: watched-literal propagation.
- `Analyze`: conflict analysis and unsat-core extraction.
- `Vsids`: decision heuristic, with a bucket mode for local-domain solving.
- `Domain`: transparent cone-of-influence control for each query.
- `Simplify`: periodic clause simplification, subsumption, equality cleanup, and garbage collection.

### Transparent COI pruning

The most important GipSAT detail for IC3 is automatic local-domain solving
(`DagCnfSolver::dcs_solve`) starting a `new_round`. That round:

1. Backtracks to level 0 and removes temporary clauses.
2. Adds temporary constraint clauses under an activation literal when needed.
3. Builds a local variable domain from explicit domain variables, assumptions, and constraints.
4. Recursively closes that domain over `DagCnf::dep(v)`, so all logic needed to decide those variables is included.
5. Runs VSIDS over that local domain instead of blindly deciding every variable in the full transition relation.

This is effectively transparent cone-of-influence pruning per SAT call. IC3
code can ask "is this cube inductive?" and GipSAT restricts decisions to the
cone of the cube, its next-state literals, and any temporary constraints:

- `inductive` checks relative induction with assumptions on next-state cube literals and optionally adds the strengthening constraint.
- `inductive_core` reads `unsat_has(next(lit))` to shrink a cube after an UNSAT result.
- MIC level 0 carries the original next cube in a temporary state constraint alongside the changing cube constraint, so repeated literal-dropping queries include those dependencies.
- Normally `add_perma_clause` expands the fixed domain with the simplified clause's dependencies. With `--guard-domain`, frame lemmas instead register directed latch edges in `Domain`; frame call sites use the same API.

Guarded mode samples an initial model after `remove_gate_init`, respecting
constraints, and completes omitted latch values with false. Each lemma selects
one satisfying latch literal as its least-seen source. When that source enters
the domain, all variables of the lemma enter it. This is the singleton rule,
not the full rule requiring every initial-model-satisfying literal to enter.
Guard edges are traversed inside ordinary DAG closure. Removed/subsumed clauses
can leave conservative extra edges. Guard mode is opt-in, excludes INN, and
does not affect preprocessing solvers. Its unsatisfiable-init early exit
currently bypasses certificate generation.

### Solver behavior worth remembering

- Assumptions are stored in `solver.assump` and are later used by predecessor lifting.
- Temporary constraints are clauses guarded by `constrain_act`; they are cleaned between rounds.
- `DagCnfSolver::dcs_solve` can return `None` when its restart budget is exhausted.
  ordinary calls pass `u32::MAX` and unwrap the result.
- After more than 10 restarts with bucket VSIDS, search switches away from bucket mode for that round.
- Periodic simplification runs roughly every 100 solves; lemma subsumption kicks in after enough lemma growth.
- `use_phase_saving` exists and is disabled in some simulation/reachability searches where diverse models are more useful.

## Core Data Structures

### `Var` and `Lit` `src/lib.rs`.

- `Var(0)` is the constant variable.
- A `Lit` is a packed `u32` literal. Use methods like `lit.var()`, `lit.polarity()`, `!lit`, `lit.not_if(...)`, and `var.lit()` instead of doing arithmetic manually.
- Do not assume DIMACS polarity conventions when editing internal code. Follow the local APIs.

### `LitVec`, `LitOrdVec`, and `LitVvec` `src/logic/lit*vec.rs`

- `LitVec` is the general literal vector with helpers for simplification, subsumption, intersection, and resolution.
- `LitOrdVec` is the ordered/canonical form used heavily for lemmas, cubes, and proof-obligation states.
- `LitVvec` is a vector of `LitVec` clauses/cubes, with CNF helpers such as XOR encodings and subsumption simplification.

IC3 often represents a cube as `LitVec` or `LitOrdVec`, and a lemma clause as the negation of that cube. Be explicit about which side of that duality you are editing.

### `VarMap`, `LitMap`, and dense maps `src/logic/varmap.rs`.

These are dense vector-backed maps indexed by `Var` or `Lit`. They are fast and common in the solver. Always `reserve(var)` before indexing newly introduced variables.

### `BitVec` `src/logic/bitvec.rs`.

This is a compact simulation bitset, not a symbolic bit-vector term. It is used by `scorr` and `frts` to store random/reachable signatures and compare candidate equivalent signals.

### `DagCnf` and `Cnf` `src/logic/dagcnf/`, `src/logic/cnf.rs`.

- `DagCnf` is the main relation representation for bit-level IC3 and preprocessing. It stores clauses per defined variable and exposes dependency information through `dep(v)`.
- `Cnf` is flatter and used by no-dependency unrolling paths.
- `new_and`, `new_or`, `new_imply`, simplification, topological sorting, and rearrangement are local APIs. Prefer them over ad hoc clause construction.

### `Transys` `src/transys/mod.rs`.

`Transys` is the bit-level transition system:

- `input`: input variables.
- `latch`: latch/state variables.
- `next`: map from latch to next-state literal.
- `init`: map from latch to optional initial literal.
- `bad`: bad property literals.
- `constraint`: invariant constraints.
- `justice`: liveness/justice properties.
- `rel`: `DagCnf` transition relation.

Important helpers:

- `ts.next(lit)`: next-state literal for a latch literal.
- `ts.lits_next(cube)`: next-state cube.
- `ts.cube_subsume_init(cube)`: whether a cube is compatible with initial constants.
- `ts.inits()`: CNF for initial-state conditions.
- `ts.load_init`, `ts.load_trans`: load a dependent transition system into CaDiCaL.
- `NoDepTransysUnroll::load_trans` and `load_trans_k`: separately load an unrolled no-dependency transition system into CaDiCaL and Kissat for BMC/K-induction.
- `ts.remove_dep()`: convert to no-dependency form for BMC/K-induction.

### `Restore` `src/transys/certify.rs`.

Preprocessing rewrites variables. `Restore` maps proofs and witnesses back to the original model. If you add preprocessing, simplification, or variable replacement, update `Restore` correctly or certificates/witnesses will be wrong.

## Portfolio runner

`ric3` provides primitive solver commands, not proof orchestration.
Portfolio-style benchmark are run by the scripts in `./tools`.
`tools/run-ric3.py` expands presets such as `all-portfolio`,
`ic3Only-portfolio`, `ctgDuel-portfolio`, and `kind-portfolio` into groups of
`ric3 check ...` commands that can run concurrently under `tools/batchrunner`.

`--preproc-file-fmt 'TESTCASE.preproc'` adds `--preproc-file <model-path>.preproc`
to each ric3 command before its engine subcommand. The suffix is appended to
the full filename (e.g. `design.aig.preproc`), and paths containing spaces remain
one argv item. Use preset `preproc` to export once per testcase, then the same
template with a solver preset to load.
In distributed mode (`-a ADDR -p PORT`), solver, testcase, and cache paths must
be accessible on every worker.

```sh
tools/run-ric3.py -i /cases -m preproc -s /bin/ric3 --preproc-file-fmt TESTCASE.preproc
tools/run-ric3.py -i /cases -m all-portfolio -s /bin/ric3 --preproc-file-fmt TESTCASE.preproc
```

Custom preset files contain solver arguments after `check TESTCASE`; update any
old `--flag=false` spellings to the new `--no-*` options before a cluster run.

```sh
# Compile the portfolio runner first
cc -O2 -pthread tools/batchrunner.c tools/batchrunner-main.c \
  -o tools/batchrunner -lnuma
# Default IC3:
ric3 check model.aig ic3
# Trivial preprocessing only and no CTG:
ric3 check model.aig --no-scorr --no-frts ic3 --no-ctg --no-drop-po
# Aggressive static CTG:
ric3 check model.aig ic3 --ctg-max 5 --ctg-limit 15 --no-drop-po
# Dynamic EXCTG:
ric3 check model.aig ic3 --dynamic --no-drop-po
# MAB EXCTG:
ric3 check model.aig ic3 --mab --no-drop-po
# Internal signals plus propagation repair:
ric3 check model.aig ic3 --inn --ctp
# Local abstraction:
ric3 check model.aig ic3 --abs-cst
ric3 check model.aig ic3 --abs-cst --abs-trans
# K-induction with simple path:
ric3 check model.aig kind --simple-path
# Shallow bug hunting:
ric3 check model.aig bmc
```

## Danger Zones

### RLive `src/rlive/mod.rs`
RLive requires a justice property. It internally creates IC3 reachability
checks, builds "shoals", and concatenates witnesses. Currently immature.

### Word-level BMC and word-level K-induction `src/wlbmc.rs`, `src/wlkind.rs`
These use Bitwuzla over a word-level transition system, currently immature.

## Development Notes

Agents are powerful at local reasoning but struggles on long, noisy context.
Therefore, preserving clean *context* as opposed to clean *code* is the ultimate goal.

The code tree strives for localized, self-contained modules over abstraction
and reusability. An agent working on one subsystem should be able to find and
load nearly all of its internal logic with a few targeted file reads and
greps, and those greps should contain little noise from unrelated subsystems.
Grep the full concrete operation names which are intended to be noise-free.

This goal is not yet fully achieved: some logic remains scattered across the
tree. Major sources of navigation noise have already been removed, however,
including runtime polymorphism, unrelated same-name functions, and helper
functions or types used only once. Preserve and improve that locality when
changing the architecture; do not introduce shared abstractions merely for
reuse when keeping concrete logic together makes the relevant subsystem easier
to inspect.

As a practical guide, unless highly reusable, functions should be **at LEAST**
25 lines long. Otherwise the context pollution caused by the extra hop hurts more.
Clean context is the ultimate goal. Dirty code is the necessary, worthy sacrifice.
