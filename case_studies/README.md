# Case studies and verified results

There are five studies, with the adjoint study split into two presentations.
Each linked README gives a file inventory.

| Case study | Resource discipline | Main proved results |
|---|---|---|
| [DualMode](DualMode/README.md) | arbitrary two-mode system, `Hi >= Lo` | Substitution, progress, preservation, weak normalization |
| [Substructural](Substructural/README.md) | arbitrary `ModeSystem` | Transport of typing along mode-system morphisms, let-elimination. |
| [AdjointND](AdjointND/README.md) / [AdjointSeq](AdjointSeq/README.md) | arbitrary `ModeSystem` | Equivalence of both calculi, open-similarity precongruence via Howe's method |
| [SessionPi](SessionPi/README.md) | one linear mode | Subject reduction, syntactic type safety |
| [GradedLinAff](GradedLinAff/README.md) | linear and affine modes with semiring multiplicities | Substitution, progress, preservation, exact/bounded use at natural-number grades |

The development declares no axioms of its own and contains no admitted proofs.
Results depend on at most `functional_extensionality_dep` from the Standard
Library. This can be verified directly in Rocq with:

```coq
Print Assumptions <theorem>.
```
