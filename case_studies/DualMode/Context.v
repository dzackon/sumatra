(** * Contexts for the dual-mode substructural λ-calculus *)

Set Implicit Arguments.

From Sumatra Require Import Modes Multiplicity Contexts.
From Sumatra.CaseStudies.DualMode Require Import Syntax.

Local Open Scope dualmode_scope.

(** Short spellings for the two distinguished modes. *)
Notation Lo := mode_lo.
Notation Hi := mode_hi.

(** Dual-mode assumptions pair a type with a mode drawn from a
    two-mode system and a binary availability annotation. *)
Definition ctx {M : Type} (n : nat) : Type :=
  fctx n ty M Avail.

Arguments ctx {M} n.
