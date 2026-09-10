# SessionPi — a session-typed π-calculus

A name-passing variant of the linearity challenge from the
[Concurrent Calculi Formalisation Benchmark](https://concurrentbenchmark.github.io/),
based on the finite session π-calculus of
[Gay and Vasconcelos](https://doi.org/10.1017/9781009000062).

Contexts are `fctx n ty Lin.Mode Avail`: one linear mode and binary
availability.

## Main results

| Benchmark item | Result | File |
|---|---|---|
| Lemmas 1–2 | `typing_ren`, `exch_top`, `typing_weak_top`, `typing_weak_join`, `strengthening` | [Structural.v](Structural.v) |
| Lemma 3 | `typing_substitution` | [Substitution.v](Substitution.v) |
| Lemmas 4–5 | `preservation_scong` | [Congruence.v](Congruence.v) |
| Theorem 1 | `step_preservation` | [Preservation.v](Preservation.v) |
| Theorem 2 | `type_safety`, `step_well_formed` | [Safety.v](Safety.v) |

## File guide

| File | Contents |
|---|---|
| [Syntax.v](Syntax.v) | Session types, duality, processes, and process renaming. |
| [Context.v](Context.v) | Context alias and `live`/`spent` entries. |
| [Typing.v](Typing.v) | Typing and `sessionpi_scope`. |
| [Dynamics.v](Dynamics.v) | Structural congruence and reduction. |
| [Examples.v](Examples.v) | Examples of typed processes. |
| [Structural.v](Structural.v) | Renaming, exchange, weakening, and strengthening. |
| [TypingInversion.v](TypingInversion.v) | Inversion and unused-entry lemmas. |
| [Substitution.v](Substitution.v) | Resource transfer by name redirection. |
| [Congruence.v](Congruence.v) | Typing under structural congruence. |
| [Preservation.v](Preservation.v) | Subject reduction. |
| [WellFormedness.v](WellFormedness.v) | Prefixes, compatibility, and well-formedness. |
| [WellFormednessTyping.v](WellFormednessTyping.v) | Connection between typing and prefix compatibility. |
| [Safety.v](Safety.v) | Type safety. |
