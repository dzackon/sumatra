(** * Shared contexts for the adjoint calculi

    The natural-deduction and sequent presentations use exactly the same
    Sumatra context representation. Keeping the alias here makes that common
    domain explicit. *)

From Sumatra Require Import Modes Multiplicity Contexts.
From Sumatra.CaseStudies.AdjointND Require Import Syntax.

Local Open Scope adjointnd_scope.

(** Adjoint assumptions pair an adjoint type with a mode and an availability
    annotation. *)
Definition ctx {M : Type} (n : nat) : Type :=
  fctx n (@ty M) M Avail.

Arguments ctx {M} n.
