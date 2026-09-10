# DualMode — a dual-mode substructural λ-calculus

A λ-calculus parameterized by `DualModeSystem M`, which has two distinct modes
`Hi ≥ Lo`. Choosing DILL makes `Lo` linear and `Hi` unrestricted; choosing
judgmental S4 makes them truth and validity, both structurally unrestricted.

Contexts are `fctx n ty M Avail`. The language has functions and boxes, with
abstraction binding at `Lo`. Box introduction constrains the live resources of
its payload to `Hi`. Unlike AdjointND, the variable rule does not impose an
independence bound.

## Main results

| Main result | File |
|---|---|
| `typing_ren`, `exch_top`, `typing_weak_top`, `typing_weak_join`, `strengthening` | [Structural.v](Structural.v) |
| `typing_substitution`, `typing_substitution_one` | [Substitution.v](Substitution.v) |
| `progress` | [Progress.v](Progress.v) |
| `step_preservation`, `eval_preservation`, `mstep_preservation` | [Preservation.v](Preservation.v) |
| `weak_normalization` (closed terms, weak reduction) | [WeakNormalizationClosed.v](WeakNormalizationClosed.v) |
| `weak_normalization` (open terms, Kripke predicate, full reduction) | [WeakNormalizationOpen.v](WeakNormalizationOpen.v) |

## File guide

| File | Contents |
|---|---|
| [Syntax.sig](Syntax.sig) | Autosubst 2 signature `Syntax.v` was generated from; see preamble of [Syntax.v](Syntax.v). |
| [Syntax.v](Syntax.v) | Types, well-scoped terms, generated renaming and substitution infrastructure. |
| [Context.v](Context.v) | The `ctx` alias. |
| [Typing.v](Typing.v) | Typing and `dualmode_scope`. |
| [Dynamics.v](Dynamics.v) | Weak small-step reduction and evaluation. |
| [DynamicsFull.v](DynamicsFull.v) | Full (strong) reduction. |
| [DerivedRules.v](DerivedRules.v) | Derived typing rules. |
| [Examples.v](Examples.v) | Examples of well-typed terms. |
| [Structural.v](Structural.v) | Structural lemmas. |
| [Substitution.v](Substitution.v) | Typed allocations through `subst_alloc`. |
| [Progress.v](Progress.v) | Canonical forms and progress. |
| [Preservation.v](Preservation.v) | Single-step type preservation. |
| [WeakNormalizationClosed.v](WeakNormalizationClosed.v) | Normalization by a logical predicate over closed terms. |
| [WeakNormalizationOpen.v](WeakNormalizationOpen.v) | A Kripke-style predicate proving reachability of values under full reduction. |
