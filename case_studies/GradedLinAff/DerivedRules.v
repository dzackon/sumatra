(** * Derived typing rules for the linear/affine graded λ-calculus *)

Set Implicit Arguments.

From Sumatra.Autosubst Require Import fintype.
From Sumatra Require Import Multiplicity Contexts Semiring SemiringContext.
From Sumatra.CaseStudies.GradedLinAff Require Import Syntax Context Typing.

Local Open Scope sumatra_scope.
Local Open Scope graded_linaff_scope.

Section DerivedRules.
  Context {R : Type} {GA : LinearGradeAlgebra R}.
  #[local] Instance SR : Semiring R := @grade_semiring R GA.
  #[local] Instance MA : MultAlgebra R := @sr_mult_algebra R SR.

  (** A grade-one singleton types its distinguished variable. *)
  Lemma ctx_singleton_typing {n} (Δ : ctx R n) (x : fin n) :
    ctx_unit_singleton Δ x ⊢ tm_var x : (Δ x).(res).
  Proof.
    eapply ht_var with (Δr := ctx_zero (ctx_unit_singleton Δ x)).
    - apply res_ctx_unit_singleton.
    - rewrite ctx_unit_singleton_idem; apply ctx_join_zero_r.
    - intro i; apply entry_weak_zero.
  Qed.

End DerivedRules.
