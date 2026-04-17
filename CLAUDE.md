# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

`VerifDemo` is a Lean 4 verification demo (Lean toolchain `leanprover/lean4:v4.29.0`, built with Lake) covering discrete math, transition systems, NuXMV-style model checking, program verification (IMP + Hoare logic), and a full formalization of the distributed cellular flows protocol from Johnson & Mitra (TCS 2015). It pairs with a Python translator that converts NuXMV `.smv` models into Lean files targeting the in-repo `TransitionSystem` framework. Most modules are pure Lean 4 core; `VerifDemo/CellularFlows/EuclideanModel.lean` uses Mathlib (v4.29.0) for Euclidean ℝ² positions — run `lake exe cache get` before first build.

## Common commands

First-time setup (pulls Mathlib cache — saves ~30min of initial compile):
```bash
lake update        # pulls Mathlib (~5-10 min with cache download)
lake exe cache get # pulls precompiled Mathlib .olean files
```

Build everything (proofs are checked at build time):
```bash
lake build
```

Build a single module (faster iteration on one file):
```bash
lake build VerifDemo.NuXMV.CounterProofs
lake build VerifDemo.CellularFlows.MultiColorProofs
```

Regenerate a `NuXMV/*.lean` from its `.smv` source:
```bash
pip install -r scripts/requirements.txt   # first time only
python scripts/smv2lean.py models/counter.smv VerifDemo/NuXMV/Counter.lean
```

CI: `.github/workflows/lean_action_ci.yml` runs `lake build` on push/PR via `leanprover/lean-action@v1`.

## Architecture

The Lean side is one Lake library (`VerifDemo`) layered as:

1. **Foundations** — [VerifDemo/TransitionSystem.lean](VerifDemo/TransitionSystem.lean) defines `TransitionSystem` (init predicate + step relation), `Reachable` (inductive closure), `InductiveInvariant`, and the soundness theorem `inductive_invariant_holds`. Also provides k-step reachability (`ReachableInK`, `k_induction`), ranking functions (`IsRankingFunction`, `ranking_bounded_progress`), execution types (`Execution`, `Eventually`, `FairFor`). Every NuXMV-derived module and CellularFlows module instantiates this structure — **read this file first** when touching any proof.

2. **Generated models** — [VerifDemo/NuXMV/](VerifDemo/NuXMV/) contains files produced by `scripts/smv2lean.py`. **Do not hand-edit `Counter.lean`, `Gcd.lean`, `Mutex.lean`, `Cellular3.lean`** — they will be overwritten; the file headers state this. Each generated file emits an enum/struct for state, a `<Name>TS : TransitionSystem <Name>State` value, and `theorem` stubs (with `sorry`) for every `INVARSPEC`. Real proofs go in the sibling `*Proofs.lean` file (e.g. [CounterProofs.lean](VerifDemo/NuXMV/CounterProofs.lean)).

3. **Parametric models** — [VerifDemo/Parametric/NMutex.lean](VerifDemo/Parametric/NMutex.lean) generalizes the 2-process mutex to N processes and proves mutual exclusion for all N. Uses `Fin n → ProcState` with frame conditions — this is the pattern for parametric proofs.

4. **Cellular Flows** — [VerifDemo/CellularFlows/](VerifDemo/CellularFlows/) formalizes the distributed cellular flows protocol from "Safe and Stabilizing Distributed Multi-Path Cellular Flows" (Johnson & Mitra, TCS 2015). ~2,900 lines, 123 theorems, zero `sorry`. See `Defs.lean` header for the full paper-to-Lean correspondence table. Key files:
   - `Defs.lean` — `DistVal` (finite/infinity), 1D topology, correspondence table
   - `Grid.lean` — 2D grid topology (`CellId2D`, `neighbors2D`, `manhattan`)
   - `Route.lean` / `RouteProofs.lean` — Route subroutine TS + Lemma 6 (convergence), Corollary 7
   - `CellFlows.lean` / `CellFlowsProofs.lean` — Full single-color TS + Theorem 1 (safety), Theorem 2 (liveness), Lemma 5
   - `DiscreteSafety.lean` — Axiom-free safety theorem (supersedes GapSafe axioms)
   - `MultiColor.lean` / `MultiColorProofs.lean` — Multi-color TS on 2D grid + Lemma 10-11, Corollaries 8-9, 2D route convergence

5. **Program verification** — [VerifDemo/ProgramVerif/](VerifDemo/ProgramVerif/) defines an IMP language with big-step semantics and Hoare logic in `Imp.lean`, with worked examples in `Examples.lean` and verified insertion sort (both recursive and imperative array versions) in `Sort.lean`.

Root module [VerifDemo.lean](VerifDemo.lean) imports everything; `lakefile.toml` sets `autoImplicit = false`.

## Proof patterns

**Inductive invariant** (used everywhere):
1. Define a strengthened predicate `P` (may be stronger than the target property)
2. Prove `∀ s, ts.init s → P s` (init preservation)
3. Prove `∀ s s', P s → ts.next s s' → P s'` (step preservation)
4. Bundle into `InductiveInvariant ts P`
5. Lift via `invariant_strengthening` to get the weaker property you actually want

**K-induction** (for convergence — used in RouteProofs, MultiColorProofs):
1. Use `ReachableInK ts k s` to track step count
2. Prove by induction on `k` that after `k` rounds, a step-indexed property holds
3. Use `k_induction` or `k_induction_with_invariant` from TransitionSystem.lean

**Ranking function** (for liveness — used in CellFlowsProofs):
1. Define `V : State → Nat` that decreases along transitions
2. Use `IsRankingFunction ts V guard` and `ranking_implies_eventually`

**Parametric proofs** (for all N — used in NMutex, CellularFlows):
- State has `Fin n → ComponentState` (one component per index)
- Transition picks one index `i : Fin n` with frame condition `∀ j ≠ i, unchanged`
- Case-split on which action fires; use frame to handle other components

## SMV → Lean translator

[scripts/smv2lean.py](scripts/smv2lean.py) reuses a Lark-based SMV parser ([smv_parser.py](scripts/smv_parser.py), [smv_grammar.lark](scripts/smv_grammar.lark), AST in [smv_model.py](scripts/smv_model.py)) and emits Lean targeting `VerifDemo.TransitionSystem`. Supported translations:

- Enums `{off, on}` → `inductive ModeVal`; booleans → `Bool`; bounded ranges → `Nat`
- `case…esac` → nested `if-then-else`
- `DEFINE` clauses inlined into use sites (`_inline_defines`)
- Variables without `init`/`next` become existentially quantified inputs in the step relation
- Nondeterministic choice `{a, b}` → disjunction
- `INVARSPEC` → theorem stub with `sorry`

When adding a new `.smv` model, generate the Lean file, then create a sibling `*Proofs.lean` and add both to the imports in [VerifDemo.lean](VerifDemo.lean).

## Key constraints

- `autoImplicit = false` — always declare type parameters explicitly (`{n : Nat}`, `(n : Nat)`)
- Don't derive `DecidableEq` or `Repr` on structures with function fields (like `RouteState`, `CellFlowState`)
- Mathlib is available but used ONLY in `EuclideanModel.lean` (for real Euclidean ℝ²). All other modules use Lean 4 core tactics (`simp`, `omega`, `cases`, `induction`, `by_cases`, etc.) and do not depend on Mathlib — keep it this way to preserve fast builds. `ContinuousModel.lean` provides a Mathlib-free alternative using an abstract `MetricPoint` typeclass with Nat distance.
- Generated NuXMV `.lean` files have `sorry` stubs — this is expected; real proofs go in `*Proofs.lean`
