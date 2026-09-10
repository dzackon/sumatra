(** * Contexts for the linear/affine graded λ-calculus *)

Set Implicit Arguments.

From Sumatra Require Import Modes Contexts.
From Sumatra.CaseStudies.GradedLinAff Require Import Syntax.

Local Open Scope graded_linaff_scope.

#[export] Existing Instance LinAff.ModeSystem_linaff.

(** Graded assumptions pair a grade-indexed type with one of the two modes
    [Lin] and [Aff] and a grade drawn from [R]. *)
Definition ctx (R : Type) (n : nat) : Type :=
  fctx n (@ty R) LinAff.Mode R.
