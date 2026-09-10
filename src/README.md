# Using the Sumatra library

Most of the short files directly under `src/` re-export modules that are normally
used together; the subdirectories hold the definitions and proofs themselves.

## Imports

For a calculus with binary availability, start with:

```coq
From Sumatra.Autosubst Require Import fintype.
From Sumatra Require Import Modes Multiplicity Contexts.
Import ScopedNotations.
Local Open Scope sumatra_scope.
```

Add imports as the development grows:

| Import from `Sumatra` | Responsibility | Entry point |
|---|---|---|
| `Modes` | the mode-system interface and standard mode systems | [Mode/Core.v](Mode/Core.v), then [Mode/Instances.v](Mode/Instances.v) |
| `Multiplicity` | relational multiplicity algebras, `Avail`, and optional algebraic capabilities | [Multiplicity/Multiplicity.v](Multiplicity/Multiplicity.v), then its [instances](Multiplicity/MultiplicityInstances.v) |
| `Contexts` | entries, contexts, maps, predicates, context join, join families, renaming | [Context/Base.v](Context/Base.v), [Context/Predicates.v](Context/Predicates.v) |
| `Join` | the core context-join relation, its algebra, and zero laws | [Context/JoinCore.v](Context/JoinCore.v), [Context/JoinZero.v](Context/JoinZero.v) |
| `Renaming` | context transport along arbitrary and bijective renamings | [Renaming/Core.v](Renaming/Core.v), [Bijections.v](Renaming/Bijections.v), [Instances.v](Renaming/Instances.v) |
| `Substitution` | context allocations for simultaneous substitutions and their structural operations | [Substitution/Core.v](Substitution/Core.v), then [Operations.v](Substitution/Operations.v) and [Split.v](Substitution/Split.v) |
| `Semiring` | semiring interfaces and the standard semiring carriers | [Multiplicity/Semiring.v](Multiplicity/Semiring.v) |
| `SemiringContext` | context scaling and singleton contexts over semiring multiplicities | [Context/Scaling.v](Context/Scaling.v) |
| `WeightedSubstitution` | weighted context allocations for quantitative substitutions | [Substitution/Weighted.v](Substitution/Weighted.v) |
| `Tactics` | automation for context or structural proofs | [Automation/Tactics.v](Automation/Tactics.v), [Structural.v](Automation/Structural.v) |

The three top-level modules that are not re-exports:

| Import from `Sumatra` | Responsibility | Defined in |
|---|---|---|
| `Scope` | declares `sumatra_scope` and the `sumatra` / `sumatra_rw` hint databases | [Scope.v](Scope.v) |
| `EqDec` | the `EqDec` class, its instance for `fin n`, and the `eqdec_*` / `inv_dep` tactics | [EqDec.v](EqDec.v) |
| `AvailNotations` | the `.::` notation for consing an available entry | [AvailNotations.v](AvailNotations.v) |

`Scope` and `EqDec` are pulled in transitively by any of the modules above.
`Contexts` already includes `Join`, `Renaming`, context predicates, component
maps, join families, and availability notation, so you do not need to list them
separately. `Modes`, `Multiplicity`, and `Semiring` include their standard
instances. `All` imports the complete library.
One may also import a submodule directly, for example `Sumatra.Mode.Core`.

## Contexts and notation

`fctx n R M A` is a function `fin n -> Entry R M A`: `n` variable
positions, resources of type `R`, modes of type `M`, and multiplicities of
type `A`.

An entry `(| r, m, a |)` has projections `res`, `mode`, and `mult`.
Its mode records structural permissions; its multiplicity is the changing
usage state. An entry is **spent** when its multiplicity is `mzero`, and
**live** when it differs from `mzero`.

| Expression | Meaning |
|---|---|
| `e .: Δ` | Add a top entry at position `None`; old positions become `Some i`. |
| `∅` | The empty context: no positions. |
| `ctx_zero Δ` | Keep resources and modes, but zero every multiplicity. Not an empty context. |
| `ctx_is_zero Δ` | A proposition saying every multiplicity is already zero. |
| `ctx_upd Δ x e` | Replace one entry. |
| `ctx_consume Δ x`, `Δ[x ↦ 0]` | Consume `x`: zero its multiplicity, keeping its resource and mode. |
| `ctx_singleton Δ x` | Keep the entire entry at `x`, including its original multiplicity; zero other positions. |
| `Δ1 ⋈ Δ2 ≡ Δ` | Resources and modes agree pointwise; the two multiplicities add to the result at each position. |
| `ctx_weak Δ` | Every live entry's mode permits weakening. Spent entries can always be discarded. |
| `Δ ⊒ m` | Every entry's mode is at least `m`. |
| `Δ ⊒⁺ m` | Every **live** entry's mode is at least `m`. |
| `ctx_ren π Δ`, `Δ⟨π⟩` | Context renaming: position `i` contains `Δ (π i)`. |
| `q • Δ` | Multiply each grade by `q`; requires a semiring. |
| `ctx_unit_singleton Δ x` | Grade `sr_one` at `x`, zero elsewhere; unlike `ctx_singleton`, it does not retain `x`'s grade. |

A context renaming `π : fin k -> fin n` takes a context of size `n` to
one of size `k`. In a typical bijective typing-renaming theorem, the context
is renamed by `ren_fun` and the term by `ren_inv`.

`ctx_all P Δ` means `forall i, P (Δ i)`. The named predicates above are
special cases.

## Finding lemmas

To find a lemma, `Search` by operation: `ctx_upd_*`, `ctx_singleton_*`, `ctx_join_*`, `ctx_ren_*`, or `subst_*`. In Rocq, commands such as `Search ctx_join.`, `Check ctx_join_zero_r_eq.`, and `Print Implicit ctx_join_zero_r_eq.` can help locate relevant results and inspect their arguments.
