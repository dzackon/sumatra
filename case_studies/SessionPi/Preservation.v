(** * Benchmark Theorem 1: subject reduction *)

Set Implicit Arguments.

From Stdlib Require Import Program.Equality.
From Sumatra.Autosubst Require Import core fintype.
From Sumatra Require Import Modes Multiplicity Contexts Tactics.
From Sumatra.CaseStudies.SessionPi Require Import
     Syntax Context Typing Dynamics Structural Substitution
     TypingInversion Congruence.

Import ScopedNotations.
Local Open Scope sumatra_scope.
Local Open Scope sessionpi_scope.
Import Lin.

(* ================================================================= *)
(* Principal reductions                                              *)
(* ================================================================= *)

(** Preservation for the closing redex. *)
Lemma preservation_close {n} (Δ : ctx n) (P Q : proc n) :
  Δ ⊢ p_res (p_par (p_wait ν_x (ren_proc shift2 P))
                   (p_close ν_y (ren_proc shift2 Q))) ->
  Δ ⊢ p_par P Q.
Proof.
  intro Hty; dependent destruction Hty; dependent destruction Hty.
  dependent destruction Hty1; dependent destruction Hty2.
  pose proof (proj1 (@typing_shift2_inv n _ P Hty1)) as HP.
  pose proof (proj1 (@typing_shift2_inv n _ Q Hty2)) as HQ.
  eapply ht_par; [exact HP | exact HQ |].
  apply (ctx_join_cons_inv (proj2 (ctx_join_cons_inv H1))).
Qed.

(** Preservation for name communication. *)
Lemma preservation_com {n} (Δ : ctx n) P Q z :
  Δ ⊢ p_res (p_par (p_inp ν_x P) (p_out ν_y z Q)) ->
  Δ ⊢ p_res (p_par (ren_proc (scons z id) P) Q).
Proof.
  Ltac solve_lookup := sumatra_ctx_normalize; eassumption.
  intro Hty; dependent destruction Hty; dependent destruction Hty.
  dependent destruction Hty1; dependent destruction Hty2.
  destruct (ctx_join_entry_one_l_inv (r := ty_recv T0 U) (m := L) ν_x H2 H)
    as [HX EX2']; pose proof (EX2' (proj2 Lin_lin)) as EX2.
  destruct (ctx_join_entry_one_r_inv (r := ty_send T1 U0) (m := L) ν_y H2 H0)
    as [HY EY1']; pose proof (EY1' (proj2 Lin_lin)) as EY1.
  dependent destruction HX; dependent destruction HY.
  destruct (ctx_join_entry_one_r_inv (r := T1) (m := L) z H2 H1)
    as [EZ EZ1']; pose proof (EZ1' (proj2 Lin_lin)) as EZ1.
  assert (Hzx : z <> ν_x).
  { intro E; subst z; unfold live in EZ.
    apply (ty_recv_not_payload T1 U), (f_equal (@res _ _ _) EZ). }
  pose proof (output_names_distinct Δ2 H0 H1) as Hyz.
  pose proof (typing_substitution z Hty1 ltac:(solve_lookup)) as HP.
  rewrite ctx_upd_comm in HP by congruence.
  pose proof (typing_change_zero HP ν_y (dual U) ltac:(solve_lookup)) as HP'.
  pose proof (typing_change_zero Hty2 ν_x U ltac:(solve_lookup)) as HQ.
  rewrite ctx_upd_comm in HQ by congruence.
  eapply ht_res, ht_par; try eassumption.
  assert (Eout :
    ctx_upd (ctx_upd ((dual (ty_recv T1 U), L) .:: (ty_recv T1 U, L) .:: Δ)
              ν_x (live U)) ν_y (live (dual U))
    = (dual U, L) .:: (U, L) .:: Δ).
  { rewrite !ctx_upd_cons; reflexivity. }
  rewrite <- Eout, <- (@ctx_upd_same _ _ _ _
    ((dual (ty_recv T1 U), L) .:: (ty_recv T1 U, L) .:: Δ) z (live T1) EZ).
  do 3 (apply ctx_join_upd; [| sumatra_solve_mult]).
  exact H2.
Qed.

(* ================================================================= *)
(* Theorem 1: Subject reduction                                      *)
(* ================================================================= *)

(** Theorem 1. If [Δ ⊢ P] and [P → Q] then [Δ ⊢ Q]. *)

Theorem step_preservation {n} (Δ : ctx n) (P Q : proc n) :
  Δ ⊢ P ->
  P ⟶ Q ->
  Δ ⊢ Q.
Proof.
  intros Hty Hred; revert Δ Hty.
  induction Hred; intros Δ Hty.
  - apply preservation_close, Hty.
  - apply preservation_com, Hty.
  - dependent destruction Hty. eapply ht_res, IHHred, Hty.
  - dependent destruction Hty. eapply ht_par; [apply IHHred | | ]; eassumption.
  - eapply (preservation_scong Δ H0).
    apply IHHred, (preservation_scong Δ H); exact Hty.
Qed.
