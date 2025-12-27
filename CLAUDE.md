# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

rIC3 is a high-performance hardware model checker implementing IC3/PDR (Property Directed Reachability) algorithms. It achieved first place in both bit-level and word-level tracks at HWMCC 2024 and 2025. The codebase is written in Rust (nightly) and includes a custom SAT solver (gipsat) deeply optimized for IC3 workloads.

## Build and Test Commands

**Prerequisites**: Rust nightly toolchain is required
```bash
rustup default nightly
```

**Clone with submodules** (required for dependencies):
```bash
git clone --recurse-submodules https://github.com/gipsyh/rIC3
# If already cloned: git submodule update --init --recursive
```

**Build**:
```bash
cargo build --release    # Release build (optimized, LTO enabled)
cargo build              # Dev build (already optimized with opt-level=3)
```

**Run**:
```bash
cargo run --release -- <AIGER_OR_BTOR2_FILE>           # 16-thread portfolio (default)
cargo run --release -- -e ic3 <FILE>                   # Single-thread IC3
cargo run --release -- -e bmc <FILE>                   # Bounded model checking
cargo run --release -- -e kind <FILE>                  # K-induction
cargo run --release -- --help                          # See all options
```

**Test**:
```bash
cargo test                           # Run all unit tests
cargo test <TESTNAME>                # Run specific test matching name
cargo fmt --check                    # Format check (CI requirement)
```

**Example models**: Located in `examples/` directory with `.aig` and `.btor` files

**Docker**:
```bash
docker build -t ric3 .
docker run -v <AIGER_FILE>:/model.aig ric3 model.aig
```

## Architecture Overview

### Core Design Philosophy

rIC3 follows a layered architecture with clear separation between verification engines, transition system representations, SAT solving, and frontend parsers. The design prioritizes performance through custom data structures (DagCnf, TransysCtx) and a specialized SAT solver.

### Key Architectural Components

**1. Engine Abstraction (`src/lib.rs`)**

The `Engine` trait provides a unified interface for all verification algorithms:
- `check() -> Option<bool>`: Main verification entry point (Some(true)=UNSAT, Some(false)=SAT, None=UNKNOWN)
- `proof() -> Proof`: Generate inductive invariant certificate for UNSAT results
- `witness() -> Witness`: Generate counterexample trace for SAT results
- `statistic()`: Report performance metrics

Implementations:
- **IC3** (`src/ic3/`): Main algorithm, frame-based inductive reasoning
- **BMC** (`src/bmc.rs`): Bounded model checking with external SAT solvers
- **Kind** (`src/kind.rs`): K-induction (base case + inductive step)
- **Rlive** (`src/rlive/`): Liveness property checking (experimental)
- **Portfolio** (`src/portfolio.rs`): Runs 16 engine configurations in parallel (default mode)

**2. Transition System Layer (`src/transys/`)**

Two representations:

- **Transys** (bit-level): Clausal representation with fields `input`, `latch` (state vars), `next` (transition relation), `init`, `bad`, `constraint`. Uses `DagCnf` from logicrs for structural sharing.

- **WlTransys** (`src/wl/transys/`): Word-level representation for BTOR2 models supporting bit-vectors and arrays. Bit-blasted to Transys during preprocessing.

- **TransysCtx** (`src/transys/ctx.rs`): Optimized context for IC3 with pre-computed maps (`next_map`, `init_map`, `is_latch`) providing O(1) lookups instead of hash map access in hot paths.

Key operations:
- `preproc()`: Applies preprocessing pipeline (COI, FRTS, SCORR, simplification)
- `ctx()`: Converts to TransysCtx for IC3
- `unroll()`: Time-unrolling for BMC/Kind

**3. Frontend Layer (`src/frontend/`)**

The `Frontend` trait abstracts input format handling:
- `ts() -> Transys`: Parse and convert to transition system
- `safe_certificate()`: Generate UNSAT certificates (strengthened transition system)
- `unsafe_certificate()`: Generate SAT witnesses (counterexample traces)
- `certify()`: Validate certificates with external tools (certifaiger/cerbotor via Docker)

Implementations:
- **AigFrontend** (`src/frontend/aig/`): AIGER format (binary .aig or ASCII .aag)
- **BtorFrontend** (`src/frontend/btor/`): BTOR2 format → WlTransys → bit-blasting

**4. IC3 Algorithm (`src/ic3/`)**

Frame-based reasoning maintaining sequence F[0]...F[k] representing overapproximations of reachable states at each depth.

Key submodules:
- `frame.rs`: Stores lemmas (blocked cubes) at each depth
- `proofoblig.rs`: CTI (Counter-example To Induction) queue with priority ordering
- `block.rs`: Blocking algorithm - generalizes and blocks CTIs
- `mic.rs`: MIC (Minimal Inductive Core) generalization with CTG support
- `solver.rs`: TransysSolver wrapping gipsat with IC3-specific operations
- `localabs.rs`: Local abstraction for constraints/transitions
- `activity.rs`: VSIDS-style activity scores for variables
- `propagate.rs`: Pushes lemmas forward between frames

Algorithm flow:
1. Base case: Check if bad states reachable from init
2. Extend: Add new frame, check bad reachability at current depth
3. Block: Generalize and block CTIs using MIC
4. Propagate: Push lemmas forward
5. If F[i] = F[i+1], property proved (invariant found)

Advanced features:
- **CTG (Counter-example To Generalization)**: Use multiple CTIs for better generalization (enabled by default, `--ic3-ctg`)
- **CTP (Counter-example To Propagation)**: Improved propagation (`--ic3-ctp`)
- **INN (Internal signals)**: Use circuit structure gates as IC3 variables (`--ic3-inn`)
- **Dynamic generalization**: Adapt strategy based on proof structure (`--ic3-dynamic`)
- **Local abstraction**: Abstract away irrelevant constraints/transitions (`--ic3-abs-cst`, `--ic3-abs-trans`)

**5. SAT Solver Layer (`src/gipsat/`)**

**DagCnfSolver**: Custom CDCL solver deeply optimized for IC3 query patterns.

Key optimizations:
- **Domain-based solving**: Only decide on relevant variables (`domain.rs`)
- **Temporary clauses**: Assumptions without permanent storage
- **Equality tracking**: Maintains equivalence classes (`eq.rs`)
- **Incremental solving**: Assumption-based interface for frame queries
- **Aggressive clause management**: Specialized clause database (`cdb.rs`)

Submodules:
- `ts.rs`: **TransysSolver** - wraps DagCnfSolver with transition system semantics
  - `inductive()`: Check if cube is inductive relative to frame
  - `get_pred()`: Extract predecessor states for generalization
- `analyze.rs`: Conflict analysis and clause learning
- `propagate.rs`: Boolean constraint propagation (BCP)
- `vsids.rs`: Variable activity heuristic with bucketed heap
- `simplify.rs`: In-processing simplification

**6. Preprocessing Pipeline (`src/transys/`)**

Applied automatically before verification (disable with `--no-preproc`):

1. **COI Refinement**: Cone-of-influence reduction - removes variables not in transitive fanin of bad states
2. **FRTS** (`frts.rs`): Functionally Reduced Transys - SAT-based functional reduction finding equivalent/constant signals (time limit: `--frts-tl`, default 1000s)
3. **SCORR** (`scorr.rs`): Sequential Correspondence - finds equivalent state variables across time (time limit: `--scorr-tl`, default 200s)
4. **Simplification** (`simp.rs`): CNF simplification, topsort, gate removal
5. **Gate Init Removal**: Converts gate-based initialization to latch init values

**Restore Mechanism**: All preprocessing maintains bidirectional variable mappings enabling translation of proofs/witnesses back to the original model (`src/transys/certify.rs`).

**7. Certificate Generation (`src/transys/certify.rs`)**

- **Proof**: Strengthened transition system where `bad ∨ invariant` becomes the new bad property. Verifiable by external tools (certifaiger for AIGER, cerbotor for BTOR2).
- **Witness**: Sequence of state/input assignments reaching bad state. Generated by traversing CTI chain to frame 0.
- **Restore**: Maps simplified variables back through all preprocessing transformations to original model variables.

### Data Flow

```
Input (AIG/BTOR2)
  ↓
Frontend parses → Transys/WlTransys
  ↓
Preprocessing (COI → FRTS → SCORR → Simplify) + Restore mapping
  ↓
TransysCtx creation (for IC3)
  ↓
Verification Engine (IC3/BMC/Kind/Portfolio)
  ↓
Result: UNSAT → Proof | SAT → Witness | UNKNOWN
  ↓
Restore to original model
  ↓
Certificate generation + optional external verification (--certify)
```

### Module Dependencies

```
main.rs
├─ config.rs: CLI parsing
├─ frontend/{aig,btor}: Input parsers
│  └─ wl/transys: Word-level representation
├─ transys: Core transition system + preprocessing
│  ├─ ctx: TransysCtx for IC3
│  ├─ certify: Proof/Witness generation + restore
│  ├─ frts, scorr: Preprocessing algorithms
│  └─ unroll: Time unrolling for BMC/Kind
├─ Engines:
│  ├─ ic3: Main IC3 algorithm
│  │  ├─ frame, proofoblig: Frame management + CTI queue
│  │  ├─ block, mic: Blocking + generalization
│  │  ├─ solver: TransysSolver wrapper
│  │  └─ localabs: Local abstraction
│  ├─ bmc, kind: Alternative engines
│  ├─ rlive: Liveness checking
│  └─ portfolio: Parallel portfolio
└─ gipsat: Custom SAT solver
   ├─ ts: TransysSolver
   ├─ analyze: Conflict analysis
   ├─ propagate: BCP
   └─ vsids: Variable ordering
```

## Development Notes

**Rust Edition**: Uses `edition = "2024"` (nightly required)

**Profile Configuration**:
- Dev builds use `opt-level = 3` for acceptable performance during development
- Release builds enable LTO, panic=abort, and stripping

**External Dependencies**:
- `aig-rs`, `btor-rs`: Format parsers (local path dependencies in `deps/`)
- `cadical-rs`, `kissat-rs`: External SAT solver bindings for BMC/Kind (local in `deps/`)
- `logicrs`: Logic utilities including DagCnf data structure (local in `deps/`)

**Submodules**: The `deps/` directory contains git submodules. Always use `--recurse-submodules` when cloning or update with `git submodule update --init --recursive`.

**CI Requirements** (`.github/workflows/ci.yml`):
- Format check: `cargo fmt --check`
- Build: `cargo build`
- Unit tests: `cargo test`
- Integration tests: Runs example models with `--certify` flag and validates exit codes (10=SAT, 20=UNSAT, 30=UNKNOWN)
- Certificate verification: Uses Docker images `ghcr.io/gipsyh/certifaiger` and `ghcr.io/gipsyh/cerbotor`

**Exit Codes**:
- 10: SAT (property violated, counterexample found)
- 20: UNSAT (property holds, invariant found)
- 30: UNKNOWN (timeout or inconclusive)
- 124: Interrupt with statistics (when `--interrupt-statistic` is enabled)

**Common CLI Options**:
- `-e, --engine <ENGINE>`: Choose engine (ic3, bmc, kind, rlive, portfolio)
- `--certificate <PATH>`: Write certificate to file
- `--certify`: Verify certificate with external tool (requires Docker)
- `--witness`: Print counterexample witness to stdout for SAT results
- `--start <N>`, `--end <N>`: Bound range for BMC/Kind
- `--rseed <N>`: Random seed for reproducibility
- IC3 options: `--ic3-ctg`, `--ic3-dynamic`, `--ic3-inn`, `--ic3-abs-cst`, etc.
- Preprocessing: `--no-preproc`, `--no-frts`, `--no-scorr`, `--frts-tl <SECONDS>`, `--scorr-tl <SECONDS>`

**Portfolio Mode** (default): Launches 16 worker processes with different configurations, each with memory limit (`--pworker-mem-limit`, default 16GB). First to finish wins, others terminated.

**Environment Variables**:
- `RUST_LOG`: Set logging level (default: "info" if not set)
- `RIC3_WORKER`: Internal flag indicating portfolio worker process (suppresses some output)

**Performance Considerations**:
- TransysCtx provides O(1) lookups critical for IC3's hot path
- DagCnf (from logicrs) uses structural sharing to reduce memory for large CNFs
- gipsat is tuned for IC3's query patterns (inductive checks, minimal unsat cores)
- FRTS/SCORR preprocessing can dramatically reduce problem size but have time budgets
- Portfolio mode exploits parallelism to handle diverse problem characteristics

## Local Abstraction: rIC3 vs ABC

### Overview

Local abstraction in IC3/PDR allows selectively ignoring irrelevant state variables and constraints during search. Both rIC3 and ABC's PDR implementation support this optimization, but use different refinement strategies when spurious counterexamples are detected.

### rIC3's Approach (Current Implementation)

**Location**: `src/ic3/localabs.rs`

**Abstraction Mechanism**:
- Uses **optional variables** (`opt` map) to control which constraints/transitions are active
- When `--ic3-abs-cst` is enabled: Each constraint `c` gets an optional variable `opt(c)`, only enforced when `opt(c)` is true
- When `--ic3-abs-trans` is enabled: Latch connections replaced with optional equality constraints controlled by optional variables
- `refine` set tracks which variables are currently **present** (non-abstracted)

**Refinement Strategy**:
- When spurious CEX detected (reaches frame 0), use **BMC (Bounded Model Checking)** to verify
- Unroll transition system to the CEX depth using `TransysUnroll`
- Load all transitions into BMC solver with optional abstraction clauses
- Extract which optional variables must be active (from BMC solver's satisfying assignment)
- Add those variables to `refine` set and constrain their optional variables to true

**Key Code Locations**:
- Abstraction setup: `LocalAbs::new()` (localabs.rs:25-89)
- BMC-based refinement: `IC3::check_witness_by_bmc()` (localabs.rs:212-257)
- Abstraction-aware unrolling: `LocalAbs::unroll_with_abstraction()` (localabs.rs:124-173)

### ABC's Approach (Reference Implementation)

**Location**: `deps/abc-demo/src/proof/pdr/` (specifically `pdrTsim3.c`)

**Abstraction Mechanism**:
- Uses **priority vector** (`vPrio`/`vAbsFlops`) where entry `i` indicates if flop `i` is:
  - **Priority 1**: Present (included in abstraction)
  - **Priority 0**: Abstracted (treated as pseudo-primary input, free variable)
- Abstracted flops are structurally converted to PPIs (Pseudo-Primary Inputs) in the AIG

**Refinement Strategy - Ternary Simulation**:
1. **Collect TFI Cone**: Traverse backward from the cube to find all variables in transitive fanin
2. **Separate Variables**: Classify cone variables into PIs, present flops, and abstracted flops
3. **Get SAT Assignment**: Read actual 0/1 values for all cone variables from SAT solver
4. **UNSAT Core Query**:
   - Add NOT(cube) as a clause with activation literal
   - Assume all cone variable assignments (from SAT model)
   - Solve (must be UNSAT since original was SAT)
   - Extract **UNSAT core** - identifies which assumptions were actually necessary
5. **Refine**: Add abstracted flops from UNSAT core to present set (priority 1)
6. **Result Handling**: Abstracted flops in the generalized cube are moved to PI literals, not state literals

**Key Code Locations**:
- Ternary simulation: `Txs3_ManTernarySim()` (pdrTsim3.c:188-354)
- Cone collection: `Txs3_ManCollectCone()` (pdrTsim3.c:140-169)
- Abstraction handling: Lines 328-339 (moves abstracted flops to PI literals)
- Refinement: `Pdr_ManDeriveCexAbs()` (pdrMan.c:458-540)

### Comparison

| Aspect | rIC3 | ABC |
|--------|------|-----|
| **Abstraction Encoding** | Optional variables control clauses | Priority vector, PPIs in AIG |
| **Spurious Detection** | BMC unrolling + SAT check | Implicit (CEX reaches frame 0) |
| **Refinement Query** | BMC solver on full unrolling | Ternary sim: UNSAT core on cube-specific TFI cone |
| **What to Extract** | Variables from BMC satisfying assignment | Variables from ternary sim UNSAT core |
| **Scope** | Entire trace from init to bad | Single cube's TFI cone |
| **Precision** | Coarse (full trace context) | Fine (cube-specific) |
| **Overhead** | BMC unrolling cost | TFI traversal + UNSAT core extraction |

### Key Insight: Different Questions

The fundamental difference is **what question is asked of the SAT solver**:

- **rIC3 (BMC)**: "Given this trace from init to bad, which abstracted variables must be active for the trace to be unreachable?"
  - Answer comes from the BMC solver's satisfying assignment
  - Refinement based on full trace context

- **ABC (Ternary Sim)**: "Given this specific cube and its TFI cone assignments, which variables are necessary to prove the cube leads to bad?"
  - Answer comes from UNSAT core of a targeted query
  - Refinement based on single cube's local reasoning

Ternary simulation can be **more precise** because it asks about a specific cube rather than an entire trace, potentially refining fewer variables and maintaining a more abstract search space.

### Infrastructure Already Available in rIC3

The good news: **All core components for ternary simulation already exist**!

1. ✅ **UNSAT Core Extraction**:
   - `TransysSolver::inductive_core()` (gipsat/ts.rs:129-156)
   - `DagCnfSolver::unsat_has()` (gipsat/mod.rs:401)
   - Already used extensively in MIC generalization (mic.rs:84, 133, 146)

2. ✅ **TFI Cone Traversal**:
   - `DagCnf::fanins()` (logicrs/src/dagcnf/mod.rs:186-202)
   - Collects all variables in transitive fanin of given variables

3. ✅ **Domain Restriction**:
   - `DagCnfSolver::set_domain()` and `unset_domain()` (gipsat/domain.rs)
   - Already used in `mic_by_drop_var()` (mic.rs:211-217, 251-258)
   - Restricts solver decisions to specific variable set

4. ✅ **SAT Value Extraction**:
   - `Satif::sat_value()` methods available throughout
   - Used in `get_pred()`, `down()`, etc.

### Potential Implementation for Ternary Simulation in rIC3

**Minimal changes needed** (~200 lines):

```rust
// In src/ic3/localabs.rs
impl LocalAbs {
    fn ternary_simulation_refine(&mut self, cube: &LitVec, k: usize) -> Option<LitVec> {
        // 1. Collect TFI cone using DagCnf::fanins()
        let cone_vars = self.uts.ts.rel.fanins(cube.iter().map(|l| l.var()));

        // 2. Separate by abstraction status (refine set)
        let (present_lits, abstracted_lits) = self.separate_cone_by_abstraction(&cone_vars, k);

        // 3. Create UNSAT query:
        //    - Add NOT(cube_next) with activation literal
        //    - Assume all cone variable assignments from SAT model
        let act_lit = self.uts.new_var().lit();
        let mut not_cube_next = self.uts.lits_next(cube, k).iter().map(|&l| !l).collect();
        not_cube_next.push(act_lit);
        self.solver.add_clause(&not_cube_next);

        let mut assumps = vec![!act_lit];
        assumps.extend(present_lits.iter().map(|&l| self.uts.lit_next(l, k)));
        assumps.extend(abstracted_lits.iter().map(|&l| self.uts.lit_next(l, k)));

        // 4. Solve (must be UNSAT) and extract core
        assert!(!self.solver.solve_with_assumptions(&assumps));

        // 5. Refine: Add abstracted vars in UNSAT core to refine set
        for &lit in &abstracted_lits {
            let next_lit = self.uts.lit_next(lit, k);
            if self.solver.unsat_has(next_lit) {
                self.refine.insert(lit.var());
                if let Some(&opt_var) = self.opt.get(&lit.var()) {
                    self.solver.add_clause(&[opt_var.lit()]);
                }
            }
        }

        // 6. Return refined cube (only non-abstracted)
        Some(cube.iter().filter(|&&l| self.refine.contains(&l.var())).copied().collect())
    }
}
```

**Configuration addition** (src/config.rs):
```rust
#[arg(long)]
pub ternary_sim: bool,  // Use ternary simulation instead of BMC for refinement
```

**Benefits**:
- More precise refinement (cube-specific vs. trace-specific)
- Maintains larger abstraction space longer
- Direct comparison with ABC's approach on same infrastructure

**Challenges**:
- Need helper for mapping time-stepped variables back to frame 0
- May need TransysCtx helpers: `is_input()`, `is_latch()`
- Careful integration with existing BMC-based flow

### Research Opportunity

This represents a clean A/B comparison opportunity:
- **Hypothesis**: Ternary simulation's cube-specific reasoning provides more precise refinement than BMC's trace-based approach
- **Measurement**: Refinement count, search space size, solving time
- **Implementation**: Toggle via `--ternary-sim` flag
- **Validation**: HWMCC benchmark suite

The infrastructure is already in place - primarily a matter of wiring existing components together correctly.

## Preprocessing Infrastructure: Deep Dive

### Overview of Preprocessing Pipeline

The preprocessing pipeline consists of 5 main techniques applied in sequence before any verification engine is created. All preprocessing is **engine-agnostic** and completes entirely before `struct IC3` initialization.

**Pipeline execution** (src/transys/simp.rs:127-143):
```rust
pub fn preproc(&self, cfg: &PreprocessConfig, mut rst: Restore) -> (Self, Restore) {
    let mut ts = self.clone();
    if cfg.preproc {
        ts.simplify(&mut rst);           // COI + Simplification
        if cfg.scorr {
            (ts, rst) = Scorr::new(ts, cfg, rst).scorr();
        }
        if cfg.frts {
            (ts, rst) = FrTs::new(ts, cfg, rst).fr();
        }
    }
    (ts, rst)
}
```

**Timing relative to IC3** (src/ic3/mod.rs:90-127):
```rust
pub fn new(cfg: Config, ts: Transys) -> Self {
    let ots = ts.clone();
    let rst = Restore::new(&ts);

    // ===== ALL PREPROCESSING HAPPENS HERE =====
    let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);  // Line 95

    // ===== IC3 STRUCTURES CREATED AFTER PREPROCESSING =====
    let tsctx = Grc::new(ts.ctx());                         // Line 102
    // ... rest of IC3 initialization
}
```

### Technique 1: COI Refinement (Cone of Influence)

**Location**: src/transys/simp.rs:11-73

**Algorithm**:
1. Start from bad states, constraints, and justice properties
2. BFS backward traversal through:
   - DagCnf dependency graph (`rel.dep(v)`)
   - Next-state relations (`self.next`)
   - Init relations (`self.init`)
3. Mark all reachable variables
4. Remove unmarked variables and update Restore mapping

**Properties**:
- **Completeness**: Complete - removes all variables not in transitive fanin
- **Independence**: Fully independent of verification engine
- **Cost**: O(V + E) graph traversal, very cheap

### Technique 2: SCORR (Sequential Correspondence)

**Location**: src/transys/scorr.rs

**Algorithm**:
1. **Simulation phase**: Generate reachable state patterns
   - `init_simulation(1)`: Sample initial states
   - `rt_simulation(&init, 10)`: Explore 10 time steps
2. **Candidate generation**: Group latches by bit-vector signatures
3. **Verification phase**: For each latch x and candidate y, check:
   - **Base case**: `(x ⊕ y) ∧ Init ∧ Constraints` must be UNSAT
   - **Inductive step**: `(x ≡ y) ∧ Trans ∧ Constraints ∧ (x' ⊕ y')` must be UNSAT

**SAT Query Details** (scorr.rs:39-65):
```rust
fn check_scorr(&mut self, x: Lit, y: Lit) -> bool {
    // Base: Can x≠y in initial states?
    if self.init_slv.solve(&[], [(x,y), (!x,!y)], restart_limit=10).is_sat() {
        return false;  // Can differ in init
    }

    // Inductive: Can x=y transition to x'≠y'?
    let xn = self.ts.next(x);
    let yn = self.ts.next(y);
    self.ind_slv.solve(&[], [(x,!y), (!x,y), (xn,yn), (!xn,!yn)], restart_limit=10)
               .is_some_and(|r| !r)  // Must be UNSAT
}
```

**Scope**:
- Only checks **latches** (state variables)
- Skips latches with non-constant init values (line 106-109)

**Algorithmic Limitations**:
1. **Candidate limit**: Line 119 limits checks to `max(10000/eqc.len(), 1)` per latch
   - Prevents O(n²) explosion in large equivalence classes
   - Can miss equivalences in huge classes (e.g., target ≡ a[9999] in 10000-element class)

2. **Fundamental incompleteness** (reachability issue):
   - The inductive check queries: "Does ANY state where x=y (reachable or not) transition to x'≠y'?"
   - Should query: "Does any REACHABLE state where x=y transition to x'≠y'?"
   - **Problem**: Transitions from unreachable states can cause false rejections

**Counterexample for incompleteness**:
```
input: i
latch x, init=0, next=i
latch y, init=0, next=(z ? ¬i : i)
latch z, init=0, next=z

Reachable states: z=0 always (never changes from init)
  → y = (0 ? ¬i : i) = i
  → x ≡ y on all reachable states ✓

SCORR's inductive check:
  Query: (x=y) ∧ Trans ∧ (x'≠y')
  SAT witness: x=0, y=0, z=1 (unreachable!), i=1
    → x'=1, y'=¬1=0
    → x'≠y' (SAT)
  Result: SCORR rejects equivalence ✗
```

**Why it works in practice**:
- Unreachable states with x=y are rare in real circuits
- Simulation explores reachable states, candidates typically formed from reachable equivalences
- Conservative rejections are safe (soundness preserved)

**Time budget**: `--scorr-tl` (default 200s)

### Technique 3: FRTS (Functionally Reduced Transys)

**Location**: src/transys/frts.rs

**Algorithm**:
1. **Topological sort**: Order variables by dependency (line 26)
2. **Simulation**: Generate 1000 random patterns via `ts.rel.simulation(1000)`
3. **Candidate generation**: Group variables by simulation signatures
4. **Verification**: For each variable v with candidate m:
   - Query: `(v ⊕ m)` is UNSAT?
   - If UNSAT: v and m are combinationally equivalent → merge
   - On SAT: Keep separate (not equivalent)
5. **Incremental simplification**: Every 5000 merges, run COI + BVE

**SAT Query** (frts.rs:85-89):
```rust
self.solver.solve_with_restart_limit(
    &[],
    vec![LitVec::from([m, lv]), LitVec::from([!m, !lv])],  // m ⊕ lv
    restart_limit=1,
)
```

**Scope**:
- Checks **all non-leaf variables** (internal gates)
- **Skips leaf variables** (line 75-77): inputs and latches

**Algorithmic Limitation**:
- Each variable only checked against **ONE representative** (first in simulation class)
- Variables in same class are never compared to each other

**Counterexample for incompleteness**:
```
Variables: a, b, c
Simulation: All have identical 1000-pattern signatures
Truth: b ≡ c (equivalent), but a ≢ b and a ≢ c

Candidate mapping:
  map[b] = a (a is first)
  map[c] = a

Execution:
  Check b vs a: (a ⊕ b) → SAT → b separate
  Check c vs a: (a ⊕ c) → SAT → c separate
  Never check b vs c!

Result: b ≡ c missed
```

**Time budget**: `--frts-tl` (default 1000s)

### Technique 4: Simplification

**Location**: src/transys/simp.rs:114-123

**Algorithm**:
1. COI refinement
2. `DagCnf::simplify()` with frozen variables
   - Constant propagation
   - Subsumption
   - Structural simplifications
3. Second COI pass (cleanup)
4. Constraint deduplication and sorting
5. **Rearrange** (line 75-112): Topological variable reordering
   - Moves important vars (inputs, latches, bad, constraints) to low indices
   - Improves cache locality

**Properties**:
- Always runs (no time limit)
- Preserves semantics via Restore mapping

### Technique 5: Gate Init Removal

**Location**: src/transys/others.rs:67-91

**Algorithm**:
1. Find latches with non-constant init (e.g., `init(l) = gate(x,y)`)
2. Create special "init variable" IV: `init=true, next=false`
3. Replace gate inits with constraints: `IV → (l ⊕ init_gate)`
4. All inits become constants

**Why**: IC3 requires constant initial values for efficient frame initialization

**Timing**: Runs AFTER main `preproc()`, before TransysCtx creation (ic3/mod.rs:101)

### SCORR vs FRTS: Complementary Techniques

| Aspect | SCORR | FRTS |
|--------|-------|------|
| **Type** | Sequential equivalence | Combinational equivalence |
| **Scope** | Latches only | Non-leaf variables (gates) |
| **Method** | Inductive proof (base + step) | Functional equivalence in CNF |
| **Reachability** | Considers init states | No temporal reasoning |
| **Example finds** | Synchronously toggling latches | Redundant gates (a∧b ≡ b∧a) |
| **Cannot find** | Gate equivalences | Latch equivalences |

**Key insight**: FRTS is NOT a superset of SCORR. Each finds equivalences the other cannot:
- SCORR finds latches that are equal in all reachable states (temporal)
- FRTS finds internal signals that are always equal (structural)

**Why run SCORR before FRTS**:
- SCORR reduces state space (fewer latches)
- Smaller circuit makes FRTS more efficient
- Strategic ordering: targeted → broad

### Completeness Summary

**Question**: Are FRTS/SCORR complete if restart limits and timeouts are removed?

**Answer**: No, both have algorithmic incompleteness:

1. **FRTS incompleteness**:
   - Source: Only checks against first representative in each simulation class
   - Impact: Misses equivalent pairs within same class
   - Could be fixed: Check all pairs (O(k²) per class)

2. **SCORR incompleteness** (two sources):
   - **Candidate limit**: Only checks `max(10000/n, 1)` candidates per latch
   - **Reachability gap**: Checks satisfiability, not reachability
     - Rejects equivalences when transition to x'≠y' exists from unreachable state where x=y
     - Fixing requires full reachability analysis (as expensive as model checking)

**Soundness**: Both are sound (never claim false equivalences)

**Pragmatic tradeoff**: Completeness sacrificed for scalability on large circuits

### Independence and Modularity

**All preprocessing techniques are fully independent of IC3**:
- Implemented as pure `Transys` transformations
- Use only generic `DagCnfSolver` (not IC3-specific solvers)
- Shared by all engines: IC3, BMC, Kind (see src/ic3/mod.rs:95, src/bmc.rs:27, src/kind.rs:23)
- No access to IC3 internals (frames, obligations, etc.)

**Complete isolation**: Preprocessing finishes before `TransysCtx` creation, which is the IC3-specific optimized context.
