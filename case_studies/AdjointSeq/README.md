# AdjointSeq — adjoint sequent calculus

The sequent presentation of the fragment studied in
[AdjointND](../AdjointND/README.md), following the implicit adjoint sequent
calculus of Jang, Roshal, Pfenning and Pientka
([FSCD 2024](https://doi.org/10.4230/LIPIcs.FSCD.2024.15)).
It uses arbitrary modes, binary availability, and explicit independence conditions.

Types and contexts are imported from `AdjointND.Syntax` and `AdjointND.Context`.

## Main results

| Main result | File |
|---|---|
| `seq_independence`, `seq_ren`, `seq_exch_top`, `seq_weak_top`, `seq_weak_join` | [Structural.v](Structural.v) |
| Derived continuation sequents used by the translations | [DerivedRules.v](DerivedRules.v) |
| `nd_seq_equiv` | [AdjointND/Equivalence.v](../AdjointND/Equivalence.v) |

Cut elimination is left as future work.

## File guide

| File | Contents |
|---|---|
| [Sequent.v](Sequent.v) | Sequent judgment, rules, and `adjointseq_scope`. |
| [Examples.v](Examples.v) | Example derivations. |
| [Structural.v](Structural.v) | Structural lemmas. |
| [DerivedRules.v](DerivedRules.v) | Identity and continuation rules for the equivalence proof. |
