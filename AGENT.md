# ric3 fork

README is linked to AGENT.md 'cause ric3 is so nuanced it's best to understand
before **using** it. The goal is to make the solver architecture, the useful
command-line knobs, and the local naming conventions explicit enough that one
at least vaguely knows what it is doing.

The current checkout is a Rust hardware model checker for AIGER and BTOR/BTOR2
inputs. The bit-level path is the main path. IC3/PDR is the primary engine. BMC
and K-induction are useful supporting engines. RLive and the word-level engines
exist, but are immature.

## Repository Map

- `src/main.rs`: CLI entry point. Defines `check` and `preprocess`.
- `src/config.rs`: engine and preprocessing Clap configuration.
- `src/ic3/`: bit-level IC3 engine and all IC3 tricks.
- `src/gipsat/`: custom incremental SAT solver used by IC3 and preprocessing.
- `src/bmc.rs`: bit-level bounded model checking.
- `src/kind.rs`: bit-level K-induction.
- `src/transys/`: bit-level transition-system representation, preprocessing, unrolling, witness/proof restore.
- `src/frontend/aig`, `src/frontend/btor`: parsers/frontends that build `Transys`.
- `src/logic/`: low-level `Var`, `Lit`, CNF/DAG-CNF, vector, bitset, and map utilities.
- `src/rlive/`, `src/wlbmc.rs`, `src/wlkind.rs`, `src/wltransys/`: available but not the normal path for this guide.
- `tools/run-ric3.py`: benchmark & portfolio runner.

Portfolio runs are script-driven through `./tools`, especially `tools/run-ric3.py`, rather than exposed in the Rust binary.

## Command Shape

Primary command:

```sh
ric3 check <model.aig|model.aag|model.btor|model.btor2> [preproc flags] <engine> [engine flags]
```

Examples:

```sh
ric3 check model.aig ic3
ric3 check model.aig --scorr=false --frts=false ic3 --ctg=false --drop-po=false
ric3 check model.aig ic3 --ctg-max 5 --ctg-limit 15 --drop-po=false
ric3 check model.aig ic3 --inn --ctp
ric3 check model.aig bmc --kissat --depth 65
ric3 check model.aig kind --simple-path
```

Boolean Clap switches that use `ArgAction::Set` can be disabled as `--flag=false`, for example `--ctg=false`, `--drop-po=false`, `--frts=false`, `--scorr=false`, and `--preproc=false`.

Useful top-level `check` flags:

- `--cert <path>`: write a safety or counterexample certificate.
- `--certify`: ask the frontend to certify the certificate with the external certifier path flow.
- `--witness`: print the unsafe witness.
- `--prop <id>`: preserve/check one property by index during preprocessing. If omitted and there are multiple bad properties, bit-level engines compress them with an OR at different points.

Useful `preprocess` command:

```sh
ric3 preprocess <model> --export-preproc <file>
ric3 check <model> --load-preproc <file> ic3
```

`--load-preproc` skips preprocessing and deserializes the saved bit-level `Transys` and restore information. `--fake-preproc-wait` sleeps for the recorded preprocessing time after loading, useful for fair benchmark accounting.

## Preprocessing

`Transys::preproc` has three phases when `--preproc=true`, which is the default:

1. Quick greedy/trivial simplification.
2. Sequential correlation reduction, `scorr`.
3. Functional reduction of the transition system, `frts`.

Disable all preprocessing with `--preproc=false`. Disable individual expensive phases with `--scorr=false` or `--frts=false`.

### Phase 1: quick greedy/trivial rewrites

Implemented in `src/transys/simp.rs` through `Transys::simplify`.

This phase performs:

- COI refinement from bad properties, constraints, justice signals, latches, initial values, and DAG dependencies.
- DAG-CNF simplification with frozen variables for semantically important objects.
- Constant simplification, bounded variable elimination, subsumption/self-subsumption, and clause cleanup through `DagCnfSimplify`.
- Constraint cleanup and deduplication.
- Variable rearrangement so active variables are dense and restore mappings remain correct.

This pass should almost always stay enabled. It is cheap relative to scorr/frts/IC3 and removes irrelevant cones before any engine starts.

### Phase 2: `scorr`

CLI:

- `--scorr=true|false`, default true.
- `--scorr-tl <seconds>`, default 200.

Implemented in `src/transys/scorr.rs`.

`scorr` is sequential correlation. It tries to prove that latches are equivalent or inverted-equivalent over reachable behavior, then replaces one with the other. The implementation:

- Generates initial-state simulation signatures.
- Generates reachable-transition simulation signatures.
- Buckets latch literals by equal or inverted signatures.
- Uses GipSAT to check both initial consistency and inductive preservation.
- Replaces proven correlated latches and reruns simplification.

Good cases:

- Control-heavy FSMs with duplicated state bits.
- Designs with many flops whose values are tied by reset and transition logic.
- Instances where IC3 spends time learning the same fact under many names.

Bad cases:

- Tiny bug-finding runs where preprocessing time dominates.
- Designs where random/reachable simulation produces many false candidates.
- Benchmark ablations where you need raw model behavior.

### Phase 3: `frts`

CLI:

- `--frts=true|false`, default true.
- `--frts-tl <seconds>`, default 1000.

Implemented in `src/transys/frts.rs`.

`frts` is functional reduction for the transition-system DAG. It starts with random simulation over the DAG, proposes equivalent or inverted-equivalent internal variables, and then validates those candidates with GipSAT. Proven equalities are added to the SAT solver, accumulated in a replacement map, and periodically applied to the transition system.

Good cases:

- Large combinational cones with repeated logic.
- Bit-blasted datapaths with many internal equivalent nodes.
- Proof workloads where a smaller transition relation matters more than preprocessing time.

Bad cases:

- Very shallow unsafe instances, where BMC or default IC3 would find the bug before preprocessing pays back.
- Instances where the candidate space is huge and few equivalences are real.

## Bit-Level IC3

Engine:

```sh
ric3 check <model> ic3 [flags]
```

Source: `src/ic3/`.

IC3 is the main engine. It maintains frames of lemmas over the transition system, repeatedly finds bad states at the frontier, blocks proof obligations by relative induction, generalizes blocked cubes into lemmas, pushes lemmas forward, and proves safety when a frame becomes empty or an inductive invariant is formed.

### Main loop, as implemented

The high-level flow in `IC3::check` is:

1. `prep_prop_base()` optionally performs predicate-property base handling.
2. `extend()` creates frame 0 and loads initial-state lemmas.
3. At each frontier level, repeatedly call `block()` until no bad state remains in the frontier.
4. If `get_bad()` finds a bad state, lift it into a predecessor/state cube and enqueue a `ProofObligation`.
5. `block()` pops obligations ordered by frame, trace depth, and cube size.
6. If an obligation intersects the initial condition at frame 0, IC3 returns unsafe. With local abstraction enabled, it first validates/refines the abstract witness with BMC.
7. Otherwise, check whether the obligation cube is relatively inductive using `blocked_with_ordered`.
8. If not blocked, obtain a predecessor with `get_pred`, enqueue that predecessor one frame earlier, and requeue the current obligation.
9. If blocked, extract an inductive core, minimize it with MIC/CTG, push it as far as possible with `push_lemma`, then add it to the frames.
10. When blocking at the current level is done, extend the frontier and call `propagate`.
11. `propagate` moves lemmas forward. If a frame becomes empty, the property is proved.
12. `propagate_to_inf` tries to move frontier lemmas into the infinity frame.

The implementation is not a toy PDR. Most of the performance is in the choices made inside MIC, propagation, predecessor lifting, and SAT-local domains.

### IC3 CLI flags

Current `IC3Config` flags:

- `--rseed <u64>`: random seed for cube shuffling and related randomized decisions. Default 0.
- `--time-limit <seconds>`: IC3 time limit. Default `u64::MAX`.
- `--ctg=true|false`: enable counterexample-to-generalization. Default true.
- `--ctg-max <usize>`: maximum CTG retries before shrinking by the current SAT model. Default 3.
- `--ctg-limit <usize>`: recursive blocking budget for CTG. Default 1.
- `--dynamic`: simple activity-based dynamic EXCTG/CTG parameter selection. Default false.
- `--mab`: LinUCB multi-armed-bandit parameter selection. Default false.
- `--mab-alpha <f64>`: LinUCB exploration parameter. Default 1.0.
- `--mab-lambda <f64>`: LinUCB regularization parameter. Default 0.1.
- `--ctp`: counterexample-to-propagation. Default false.
- `--inn`: internal-signal IC3. Default false.
- `--abs-cst`: local abstraction of constraints. Default false.
- `--abs-trans`: local abstraction of transition connections. Default false.
- `--drop-po=true|false`: drop over-active proof obligations. Default true.
- `--parent-lemma=true|false`: use parent lemma guidance during MIC. Default true.
- `--pred-prop`: predicate-property mode. Default false.
- `--local-proof <usize>`: local proof/property selection path. Commented as buggy; avoid unless explicitly working on it.

Important incompatibilities enforced by `IC3::new`:

- `--dynamic` and `--mab` cannot both be enabled.
- `--dynamic` cannot be combined with `--drop-po=true`.
- `--mab` cannot be combined with `--drop-po=true`.
- Since `--drop-po` defaults to true, using `--dynamic` or `--mab` requires `--drop-po=false`.
- `--inn` cannot be combined with `--abs-cst` or `--abs-trans`.

### Counterexample to Generalization, CTG

CLI:

```sh
--ctg=true|false
--ctg-max <n>
--ctg-limit <n>
```

Default:

```text
--ctg=true --ctg-max=3 --ctg-limit=1
```

Source: `src/ic3/mic.rs`.

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
- Runs with `--drop-po=false`, where the solver is allowed to keep working through hard obligations rather than dropping them.

Bad cases:

- Shallow unsafe instances. CTG may spend time polishing lemmas when BMC-like search would already find the bug.
- Instances with genuinely reachable CTGs. Recursive blocking fails and the extra calls are pure overhead.
- Very small models where default IC3 already finds an invariant quickly.

Useful recipes:

```sh
ric3 check model.aig ic3 --ctg=false --drop-po=false
ric3 check model.aig ic3 --ctg-max 5 --ctg-limit 15 --drop-po=false
```

The first recipe is useful as an ablation and sometimes for bug hunting. The second is the aggressive CTG recipe used in benchmark-style runs.

### Extended CTG and dynamic EXCTG generation

There is no separate `--exctg` flag in this checkout. Extended CTG behavior is expressed by choosing stronger `DropVarParameter` settings, either statically with `--ctg-max/--ctg-limit` or dynamically with `--dynamic` or `--mab`.

Simple dynamic mode:

```sh
ric3 check model.aig ic3 --dynamic --drop-po=false
```

Source: `src/ic3/mab.rs`, `balanced_params`.

Despite living in `mab.rs`, the simple dynamic mode does not learn. It computes a CTG parameter from proof-obligation activity along the successor chain:

- Low branch activity: use no CTG or almost no CTG.
- Medium activity: use small CTG.
- High activity: grow the CTG recursive budget and allow up to 5 CTGs.

Good cases:

- Mixed portfolios where static CTG is too expensive on easy obligations but too weak on hard ones.
- Long safe proofs where the hard obligations reveal themselves by repeated activity.
- Runs where you would otherwise hand-tune `--ctg-max` and `--ctg-limit`.

Bad cases:

- Tiny cases where the activity signal has no time to become meaningful.
- Runs where `--drop-po` behavior is desired. Dynamic mode requires `--drop-po=false`.

MAB mode:

```sh
ric3 check model.aig ic3 --mab --drop-po=false
ric3 check model.aig ic3 --mab --mab-alpha 0.7 --mab-lambda 0.1 --drop-po=false
```

Source: `src/ic3/mab.rs`, `CtgMab`.

The MAB mode uses LinUCB to choose among several CTG/generalization arms. The context vector is:

```text
[relative level, relative cube size, push potential, relative depth,
 frame saturation, activity, bias]
```

The arms include:

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
- Research/ablation around adaptive generalization.

Bad cases:

- Short runs, shallow bugs, and tiny models.
- Determinism-sensitive experiments unless `--rseed` and all benchmark context are fixed.
- Any run that still wants `--drop-po=true`.

### Counterexample to Propagation, CTP

CLI:

```sh
--ctp
```

Default false. Source: `src/ic3/propagate.rs`.

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

### Internal Signal IC3

CLI:

```sh
--inn
```

Default false. Source: `src/ic3/mod.rs`, `src/transys/unroll.rs`.

Internal-signal IC3 treats selected combinational variables as latch-like state variables. `IC3::new` performs one unroll and calls `internal_signals()` when `--inn` is enabled. Predicate-property mode has a related `internal_signals_with_full_prime()` path.

Why it helps:

- Standard IC3 lemmas are over latches. On bit-blasted circuits, the latch state can be too coarse.
- Internal combinational signals can expose useful cut points in the transition relation.
- Lemmas over these cut points can be shorter or easier to propagate.

Good cases:

- Deep combinational logic between flops.
- Designs where the useful invariant is naturally about decoded/control/internal wires.
- Bit-level HWMCC-style instances where state-only lemmas are weak.

Bad cases:

- Models where adding internal signals explodes the state space more than it helps.
- Runs using local abstraction: `--inn` is explicitly incompatible with `--abs-cst` and `--abs-trans`.
- Very small models, where the overhead is unnecessary.

Useful recipes:

```sh
ric3 check model.aig ic3 --inn
ric3 check model.aig ic3 --inn --ctp
ric3 check model.aig ic3 --inn --ctg=false
ric3 check model.aig ic3 --inn --dynamic --drop-po=false
ric3 check model.aig ic3 --inn --mab --drop-po=false
```

### Local Abstraction

CLI:

```sh
--abs-cst
--abs-trans
```

Default false. Source: `src/ic3/localabs.rs`.

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
- Runs with `--inn`, which is incompatible.
- Debugging proof production. Abstraction changes the search shape and may make traces less direct.

Useful recipes:

```sh
ric3 check model.aig ic3 --abs-cst
ric3 check model.aig ic3 --abs-cst --abs-trans
```

### Drop Proof Obligation

CLI:

```sh
--drop-po=true|false
```

Default true. Source: `src/ic3/block.rs`.

Each proof obligation has an activity score. It increments when the obligation is revisited and decays when the obligation is pushed to later frames. If `--drop-po=true` and an obligation activity exceeds 20, `block()` drops it instead of continuing to chase that branch.

Good cases:

- Portfolio-style runs where escaping a pathological obligation chain is worth it.
- Instances with many alternative bad states, where the frontier can rediscover useful work later.
- Default practical IC3 runs.

Bad cases:

- Evaluating CTG, EXCTG, dynamic, or MAB behavior. Those modes need persistent obligations and are incompatible or practically paired with `--drop-po=false`.
- Research/debugging runs where you want textbook obligation handling.
- Cases where a dropped branch is exactly the one that would have yielded the decisive lemma.

Useful recipes:

```sh
ric3 check model.aig ic3
ric3 check model.aig ic3 --drop-po=false
```

### Predicate Property

CLI:

```sh
--pred-prop
```

Default false. Source: `src/ic3/predprop.rs`.

Predicate-property mode changes how IC3 asks for frontier bad states. It builds a secondary transition system over predecessor/property predicates and uses that solver to produce bad predecessors, then lifts them back into state/input cubes.

Implementation notes:

- `PredProp::new` compiles one-step behavior, or the internal-signal variant when `--inn` is enabled.
- It adds the original bad condition as a constraint in the predicate-property system.
- `prep_prop_base` first checks for a depth-0 counterexample.
- If base is safe, the main transition system gets `!bad` as a constraint and IC3 searches predecessors instead of direct bad states.
- When frames extend, the predicate-property solver is rebuilt with infinity-frame lemmas.

Good cases:

- Cases where direct bad-state queries are too broad and predecessor queries are more informative.
- Designs with bad properties that are easy to hit syntactically but hard to lift well.
- Some multi-property/local-property experiments.

Bad cases:

- Simple bad states where direct `get_bad` is already cheap.
- Debugging the standard IC3 loop, because this changes the shape of frontier queries.

Useful recipe:

```sh
ric3 check model.aig ic3 --pred-prop
```

### Finding Parent Lemma

CLI:

```sh
--parent-lemma=true|false
```

Default true. Source: `src/ic3/mic.rs`, `src/ic3/frame.rs`.

This is the "generalize toward look-alike lemmas in parent frames" trick. During MIC, if the previous frame contains a lemma that subsumes the current cube, IC3 changes the drop order so literals outside that parent shape are tried first. The result is a generalized lemma that tends to resemble the parent lemma.

Why it helps:

- IC3 often learns families of similar lemmas across adjacent frames.
- Generalizing toward a parent can produce clauses that push better.
- It complements CTP: CTP learns missing propagation-side lemmas, while parent-lemma guidance shapes blocking-side MIC toward lemmas that already have a propagation history.

Good cases:

- Proofs with repeated, layered lemma families.
- Runs with many similar obligations across frames.
- Default safe-proof workloads.

Bad cases:

- Ablations where MIC order must be neutral.
- Rare cases where parent resemblance over-biases MIC away from a smaller unrelated lemma.

### Miscellaneous IC3 Notes

- `Activity` is used to sort literals for blocking/MIC and to score obligations for dynamic CTG.
- `ProofObligationQueue` prioritizes higher frame, shallower trace depth, then smaller cube.
- `Frame::trivial_contained` avoids adding or reblocking cubes already subsumed by known lemmas.
- `add_lemma` removes subsumed lemmas in earlier frames and can detect an empty frame as proof.
- `propagate_to_inf` tries to move frontier lemmas to an infinity frame and can recursively prove the CTP needed to do so.
- `local-proof` is present but marked buggy in source. Do not build new workflows around it without first fixing/testing it.

## BMC

Engine:

```sh
ric3 check <model> bmc [flags]
```

Source: `src/bmc.rs`.

BMC removes transition-system dependencies into a no-dependency CNF form, turns constraints into clauses, simplifies, then incrementally unrolls the transition relation and asks whether any bad property holds at each checked depth.

Current flags:

- `--start <usize>`: first bound. Default 0.
- `--end <usize>`: maximum bound/depth. Default `usize::MAX`.
- `--step <u32>`: check every Nth bound. Default 1.
- `--rseed <u64>`: seed for SAT solver randomization. Default 0.
- `--kissat`: use Kissat instead of CaDiCaL. Default false.
- `--dyn-step`: choose a step from model size, roughly `10_000_000 / (max_var + num_clauses)`.

Practical guidance:

- The useful knobs are `--kissat` and the depth bound. The code calls the depth cap `--end`; there is no literal `--depth` flag in this checkout.
- `--kissat` is often the better BMC choice for raw bug hunting.
- `--step` and `--dyn-step` are benchmark throughput knobs. They can skip the first failing depth if set too coarsely, although the engine reports the depth it actually checked.
- BMC proves nothing beyond "no counterexample up to checked bound"; it returns `UNKNOWN(bound)` after the bound is exhausted.

Good cases:

- Shallow bugs.
- Quick sanity checks before trying IC3.
- Producing unsafe witnesses.

Bad cases:

- Safe instances.
- Deep bugs unless the bound is known and affordable.

Useful recipes:

```sh
ric3 check model.aig bmc --kissat --end 50
ric3 check model.aig bmc --kissat --end 500 --step 10
```

## K-Induction

Engine:

```sh
ric3 check <model> kind [flags]
```

Source: `src/kind.rs`.

K-induction uses the same no-dependency unrolling style as BMC, with a base check and an inductive step. For each `k`, unless `--skip-bmc` is set, it first checks whether a bad state exists at depth `k - 1`. Then it asserts bad states false for previous frames and asks whether `bad@k` is impossible. If impossible, the property is K-inductive and safe.

Current flags:

- `--end <usize>`: maximum bound. Default `usize::MAX`.
- `--simple-path`: add simple-path constraints. Default false.
- `--skip-bmc`: skip the base BMC query. Default false.
- `--local-proof <usize>`: present, but `Kind::new` panics if it is used for an actual local property.

Practical guidance:

- The useful knob is `--simple-path`, plus `--end` as a sanity cap.
- `--simple-path` adds pairwise disequality constraints between the new state and all earlier states using XOR helper variables. This can make non-inductive properties inductive by ruling out loops.
- Simple path is expensive: roughly O(k^2 * number_of_latches) extra structure over time.
- `--skip-bmc` is only for special experiments. Normally keep the base check.

Good cases:

- Small to medium systems where the property is close to K-inductive.
- Counter-like systems where simple-path constraints eliminate recurrence artifacts.
- Quick proof attempts before full IC3, when a small `--end` is enough.

Bad cases:

- Large latch counts with `--simple-path`.
- Properties requiring rich auxiliary invariants. IC3 is the right engine there.

Useful recipe:

```sh
ric3 check model.aig kind --simple-path --end 200
```

## Danger Zones

### RLive

Engine:

```sh
ric3 check <model> rlive
```

Source: `src/rlive/mod.rs`.

RLive requires a justice property. It internally creates IC3 reachability
checks, builds "shoals", and concatenates witnesses. Currently immature.

### Word-level BMC and word-level K-induction

Engines:

```sh
ric3 check <model> wl-bmc ...
ric3 check <model> wl-kind ...
```

Source: `src/wlbmc.rs`, `src/wlkind.rs`, `src/wltransys/`.

These use Bitwuzla over a word-level transition system, currently immature.

## GipSAT

Source: `src/gipsat/`.

GipSAT is the custom SAT solver powering IC3, `scorr`, and `frts`. It is designed for many small, related transition-system queries rather than standalone SAT competition use.

Core pieces:

- `DagCnfSolver`: incremental SAT solver over `DagCnf`.
- `ClauseDB`: stores transition clauses, IC3 lemmas, learnt clauses, and temporary clauses separately.
- `Watchers`: watched-literal propagation.
- `Analyze`: conflict analysis and unsat-core extraction.
- `Vsids`: decision heuristic, with a bucket mode for local-domain solving.
- `Domain`: transparent cone-of-influence control for each query.
- `Simplify`: periodic clause simplification, subsumption, equality cleanup, and garbage collection.
- `Eqc`: equality tracking used by functional reduction and solver cleanup.

### Transparent COI pruning

The most important GipSAT detail for IC3 is automatic local-domain solving.

Each `solve_full` call starts a `new_round`. That round:

1. Backtracks to level 0 and removes temporary clauses.
2. Adds temporary constraint clauses under an activation literal when needed.
3. Builds a local variable domain from explicit domain variables, assumptions, and constraints.
4. Recursively closes that domain over `DagCnf::dep(v)`, so all logic needed to decide those variables is included.
5. Runs VSIDS over that local domain instead of blindly deciding every variable in the full transition relation.

This is effectively transparent cone-of-influence pruning per SAT call. IC3 code can ask "is this cube inductive?" and GipSAT restricts decisions to the cone of the cube, its next-state literals, and any temporary constraints.

Places where this matters:

- `inductive` and `inductive_with_constrain` check relative induction with assumptions on next-state cube literals.
- `inductive_core` reads `unsat_has(next(lit))` to shrink a cube after an UNSAT result.
- MIC level 0 uses `set_domain` over the current cube and next cube to constrain decisions during repeated literal-dropping tests.
- `add_clause` calls `add_domain` so new lemmas expand the fixed domain with their dependencies.

Practical consequence: do not casually bypass GipSAT with a generic SAT wrapper inside IC3. Much of rIC3's speed comes from these local domains, unsat cores, and transition-aware helper functions.

### Solver behavior worth remembering

- Assumptions are stored in `solver.assump` and are later used by predecessor lifting.
- Temporary constraints are clauses guarded by `constrain_act`; they are cleaned between rounds.
- `solve_with_restart_limit` can return `None` when the restart budget is exhausted. `scorr` and `frts` deliberately use small limits for candidate validation.
- After more than 10 restarts with bucket VSIDS, search switches away from bucket mode for that round.
- Periodic simplification runs roughly every 100 solves; lemma subsumption kicks in after enough lemma growth.
- `use_phase_saving` exists and is disabled in some simulation/reachability searches where diverse models are more useful.

## Core Data Structures

### `Var` and `Lit`

Source: `src/lib.rs`.

- `Var(0)` is the constant variable.
- A `Lit` is a packed `u32` literal. Use methods like `lit.var()`, `lit.polarity()`, `!lit`, `lit.not_if(...)`, and `var.lit()` instead of doing arithmetic manually.
- Do not assume DIMACS polarity conventions when editing internal code. Follow the local APIs.

### `LitVec`, `LitOrdVec`, and `LitVvec`

Sources: `src/logic/litvec.rs`, `src/logic/litordvec.rs`, `src/logic/litvvec.rs`.

- `LitVec` is the general literal vector with helpers for simplification, subsumption, intersection, and resolution.
- `LitOrdVec` is the ordered/canonical form used heavily for lemmas, cubes, and proof-obligation states.
- `LitVvec` is a vector of `LitVec` clauses/cubes, with CNF helpers such as XOR encodings and subsumption simplification.

IC3 often represents a cube as `LitVec` or `LitOrdVec`, and a lemma clause as the negation of that cube. Be explicit about which side of that duality you are editing.

### `VarMap`, `LitMap`, and dense maps

Source: `src/logic/varmap.rs`.

These are dense vector-backed maps indexed by `Var` or `Lit`. They are fast and common in the solver. Always `reserve(var)` before indexing newly introduced variables.

### `BitVec`

Source: `src/logic/bitvec.rs`.

This is a compact simulation bitset, not a symbolic bit-vector term. It is used by `scorr` and `frts` to store random/reachable signatures and compare candidate equivalent signals.

### `DagCnf` and `Cnf`

Sources: `src/logic/dagcnf/`, `src/logic/cnf.rs`.

- `DagCnf` is the main relation representation for bit-level IC3 and preprocessing. It stores clauses per defined variable and exposes dependency information through `dep(v)`.
- `Cnf` is flatter and used by no-dependency unrolling paths.
- `new_and`, `new_or`, `new_imply`, simplification, topological sorting, and rearrangement are local APIs. Prefer them over ad hoc clause construction.

### `Transys`

Source: `src/transys/mod.rs`.

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
- `ts.load_init`, `ts.load_trans`: load into a SAT interface.
- `ts.remove_dep()`: convert to no-dependency form for BMC/K-induction.

### `Restore`

Source: `src/transys/certify.rs`.

Preprocessing rewrites variables. `Restore` maps proofs and witnesses back to the original model. If you add preprocessing, simplification, or variable replacement, update `Restore` correctly or certificates/witnesses will be wrong.

## Practical Solver Recipes

Portfolio-style benchmark are run by the scripts in `./tools`.
`tools/run-ric3.py` expands presets such as `all-portfolio`,
`ic3Only-portfolio`, `ctgDuel-portfolio`, and `kind-portfolio` into groups of
`ric3 check ...` commands that can run concurrently under `tools/run-info`.

```sh
# Compile the portfolio runner first
cc -O2 tools/run-*.c -o tools/run-info -lnuma
# Default IC3:
ric3 check model.aig ic3
# No preprocessing and no CTG, for e.g. models taking too long to preprocess:
ric3 check model.aig --preproc=false ic3 --ctg=false --drop-po=false
# Aggressive static CTG:
ric3 check model.aig ic3 --ctg-max 5 --ctg-limit 15 --drop-po=false
# Dynamic EXCTG:
ric3 check model.aig ic3 --dynamic --drop-po=false
# MAB EXCTG:
ric3 check model.aig ic3 --mab --drop-po=false
# Internal signals plus propagation repair:
ric3 check model.aig ic3 --inn --ctp
# Local abstraction:
ric3 check model.aig ic3 --abs-cst
ric3 check model.aig ic3 --abs-cst --abs-trans
# K-induction with simple path:
ric3 check model.aig kind --simple-path --end 200
# Shallow bug hunting:
ric3 check model.aig bmc
```

## Development Notes

- Prefer `rg` for code search.
- Prefer existing solver abstractions (`Transys`, `DagCnf`, `Satif`, `new_transys_solver`, `inductive`) over manual clause plumbing.
- Be careful with cube/clause polarity. IC3 lemmas are stored as cubes in frames, but added to SAT as negated cubes.
- If a change touches preprocessing, check witness/proof restore paths.
- If a change touches IC3 tricks, test both safe and unsafe examples. Many tricks mainly affect safe proofs, but can break witness handling if they interact with abstraction or obligation chains.
- Do not rely on `tools/run-ric3.py` as exact current CLI truth. It contains useful benchmark recipes, but at least some flags in it do not match the current Clap structs.
