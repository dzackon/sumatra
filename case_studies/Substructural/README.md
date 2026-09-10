# Substructural — a multiplicative–additive λ-calculus

The full multiplicative–additive propositional fragment (`⊸`, `⊗`, `𝟏`,
`&`, `⊤`, `⊕`, `𝟎`) is parameterized by an arbitrary `ModeSystem M`.
Contexts are `fctx n ty M Avail`. Connectives stay at the conclusion's mode;
the live assumptions must lie at that mode or above it.

## Main results

| Main result | File |
|---|---|
| `independence`, `typing_ren`, `exch_top`, weakening and `strengthening` | [Structural.v](Structural.v) |
| `typing_mode_transport` | [ModeTransport.v](ModeTransport.v) |
| `typing_lin_to_sub`, `typing_aff_to_sub`, `typing_rel_to_sub`, `typing_unr_to_sub` | [ModeTransport.v](ModeTransport.v) |
| `typing_sub_to_unr` | [ModeTransport.v](ModeTransport.v) |
| `let_elim_preserves_typing` | [LetElim.v](LetElim.v) |

The theorem `typing_mode_transport` proves that typing transports along any
mode-system morphism. `let_elim_preserves_typing` proves that a let-elimination
translation preserves typing in both directions.

## File guide

| File | Contents |
|---|---|
| [Syntax.v](Syntax.v) | Types, terms, generated renaming and substitution infrastructure. |
| [Context.v](Context.v) | The `ctx` alias. |
| [Typing.v](Typing.v) | Rules and `substructural_scope`. |
| [Examples.v](Examples.v) | Examples of well-typed terms. |
| [Structural.v](Structural.v) | Independence and structural lemmas. |
| [ModeTransport.v](ModeTransport.v) | Mode morphisms, context mapping, and typing transport. |
| [LetElim.v](LetElim.v) | Let-extended syntax, typing, and elimination. |
