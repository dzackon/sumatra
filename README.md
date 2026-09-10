# Sumatra

Sumatra (**SU**bstructural **M**eta-theory with **A**djoin**T** **R**esource
**A**nnotations) is a Rocq library for mechanizing substructural logics and type
systems. It supplies infrastructure for contexts, resource splitting, renaming,
and substitutions, as well as proof tactics. The user supplies the object
language and its judgments.

Each context entry records a resource (usually a type), a **mode** describing
its structural permissions, and a **multiplicity** recording its availability
or quantity. Splitting and consumption update multiplicities without removing
variable positions.

## Build

The current sources have been checked with Rocq 9.1.1 and Stdlib 9.1.0. The
required Autosubst support files are included in [autosubst/](autosubst), so no
separate Autosubst installation is needed.

To download Rocq, run:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-stdlib
```

Then, from the repository root:

```sh
rocq makefile -f _RocqProject -o Makefile
make -j4
make html
```

The last command is optional; it produces browsable documentation in `html/`.

## Using the library

The complete public interface is available through `Sumatra.All`:

```coq
From Sumatra.Autosubst Require Import fintype.
From Sumatra Require Import All.
```

It imports the whole library, including standard instances and tactics.
For most developments, it is enough to import only the modules one
uses. The principal modules are outlined in [src/README.md](src/README.md).

## Case studies and verified results

These are five studies, with the adjoint study split into two presentations.
Each linked README gives a file inventory.

| Case study | Resource discipline | Main proved results |
|---|---|---|
| [DualMode](case_studies/DualMode/README.md) | arbitrary two-mode system, `Hi >= Lo` | Substitution, progress, preservation, weak normalization |
| [Substructural](case_studies/Substructural/README.md) | arbitrary `ModeSystem` | Transport of typing along mode-system morphisms, let-elimination. |
| [AdjointND](case_studies/AdjointND/README.md) / [AdjointSeq](case_studies/AdjointSeq/README.md) | arbitrary `ModeSystem` | Equivalence of both calculi, open-similarity precongruence via Howe's method |
| [SessionPi](case_studies/SessionPi/README.md) | one linear mode | Subject reduction, syntactic type safety |
| [GradedLinAff](case_studies/GradedLinAff/README.md) | linear and affine modes with semiring multiplicities | Substitution, progress, preservation, exact/bounded use at natural-number grades |

The development declares no axioms of its own and contains no admitted proofs.
Results depend on at most `functional_extensionality_dep` or `Eq_rect_eq`, both
from the Standard Library. This can be verified directly in Rocq with:

```coq
Print Assumptions <theorem>.
```
