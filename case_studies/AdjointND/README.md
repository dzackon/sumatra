# AdjointND — adjoint natural deduction

An adjoint natural-deduction calculus over an arbitrary `ModeSystem M`,
following Jang, Roshal, Pfenning and Pientka, *Adjoint Natural Deduction*
([FSCD 2024](https://doi.org/10.4230/LIPIcs.FSCD.2024.15)). Checking and
synthesis are merged into one typing judgment, with explicit independence
conditions. The fragment includes implication, multiplicative unit, and the two
adjoint shifts.

Types are parameterized by the mode type (`@ty M`); a typing judgment carries
a type and a conclusion mode. Contexts are `fctx n (@ty M) M Avail`.
[AdjointSeq](../AdjointSeq/README.md) reuses these types and contexts.

## Main results

The two larger proof developments are:

- [Equivalence.v](Equivalence.v) translates between natural deduction and
  sequent derivations. Its reverse direction generalizes over a well-typed
  simultaneous substitution.
- [Similarity.v](Similarity.v) through [Precongruence.v](Precongruence.v)
  develops Howe's method to prove that open similarity is a precongruence.

| Main result | File |
|---|---|
| `independence`, `typing_ren`, `exch_top`, `typing_weak_top`, `typing_weak_join`, `strengthening` | [Structural.v](Structural.v) |
| `typing_substitution`, `typing_substitution_one` | [Substitution.v](Substitution.v) |
| `eval_preservation` | [Preservation.v](Preservation.v) |
| `soundness`, `seq_to_nd`, `completeness`, `nd_seq_equiv` | [Equivalence.v](Equivalence.v) |
| `osim_precongruence` | [Precongruence.v](Precongruence.v) |

## File guide

| File | Contents |
|---|---|
| [Syntax.sig](Syntax.sig) | Autosubst 2 signature `Syntax.v` was generated from; see preamble of [Syntax.v](Syntax.v). |
| [Syntax.v](Syntax.v) | Types, terms, generated binding infrastructure. |
| [Context.v](Context.v) | Context alias shared with AdjointSeq. |
| [Typing.v](Typing.v) | Typing and `adjointnd_scope`. |
| [Dynamics.v](Dynamics.v) | Call-by-name evaluation. |
| [DerivedRules.v](DerivedRules.v) | Derived typing rules. |
| [Examples.v](Examples.v) | Examples of well-typed terms in the calculus. |
| [Structural.v](Structural.v) | Independence and structural lemmas. |
| [Substitution.v](Substitution.v) | Typed simultaneous substitutions and their operations. |
| [Preservation.v](Preservation.v) | Evaluation preserves typing. |
| [Equivalence.v](Equivalence.v) | Equivalence with AdjointSeq. |
| [Similarity.v](Similarity.v) | Closed applicative similarity and its open extension. |
| [Howe.v](Howe.v) | The Howe relation and basic properties. |
| [HoweSubstitution.v](HoweSubstitution.v) | Howe-related substitutions and substitutivity. |
| [HoweEvaluation.v](HoweEvaluation.v) | Evaluation-related supporting lemmas. |
| [HoweFundamental.v](HoweFundamental.v) | The Howe relation is a simulation and agrees with open similarity. |
| [Precongruence.v](Precongruence.v) | Open similarity is a precongruence. |
