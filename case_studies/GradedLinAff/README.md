# GradedLinAff — a linear/affine graded λ-calculus

This study uses quantitative multiplicities with two modes, `Lin` and
`Aff`, ordered `Lin ≤ Aff`. Only `Aff` admits weakening; neither admits
contraction. Contexts are `fctx n (@ty R) LinAff.Mode R`, written `ctx R n`.

Grades are drawn from a `LinearGradeAlgebra`: a semiring with `1 ≠ 0`,
no non-trivial additive decomposition of one, and no non-trivial multiplicative
factorization of one. Addition splits grades; multiplication scales contexts.
The language has multiplicative unit, functions binding at a chosen mode, and
boxes carrying a grade and a binding mode.

## Main results

| Main result | File |
|---|---|
| `typing_ren`, `exch_top`, `typing_weak_top`, `typing_weak_join`, `strengthening` | [Structural.v](Structural.v) |
| `typing_substitution`, `typing_substitution_one` | [Substitution.v](Substitution.v) |
| `progress`, `progress_no_uip` | [Progress.v](Progress.v) |
| `step_preservation` | [Preservation.v](Preservation.v) |
| `typing_uses`, `typing_lin_exact`, `typing_aff_bounded` | [Usage.v](Usage.v) |

## File guide

| File | Contents |
|---|---|
| [Syntax.v](Syntax.v) | Types and terms parameterized by grades, generated binding infrastructure. |
| [Context.v](Context.v) | The `ctx` alias, with the grade parameter explicit. |
| [Typing.v](Typing.v) | Rules and `graded_linaff_scope`. |
| [Dynamics.v](Dynamics.v) | Weak call-by-name dynamics. |
| [DerivedRules.v](DerivedRules.v) | Derived typing rules. |
| [Examples.v](Examples.v) | Derivations over the natural-number grade algebra. |
| [Structural.v](Structural.v) | Renaming, weakening, exchange. |
| [Substitution.v](Substitution.v) | Typed weighted substitution. |
| [Progress.v](Progress.v) | Closed progress. |
| [Preservation.v](Preservation.v) | Single-step preservation. |
| [Usage.v](Usage.v) | Exact and bounded annotated use for natural-number grades. |

