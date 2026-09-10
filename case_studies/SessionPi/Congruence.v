(** * Benchmark Lemmas 4--5: preservation by structural congruence *)

Set Implicit Arguments.

From Stdlib Require Import Program.Equality.
From Sumatra.Autosubst Require Import core fintype.
From Sumatra Require Import Modes Multiplicity Contexts Tactics.
From Sumatra.CaseStudies.SessionPi Require Import
     Syntax Context Typing Dynamics Structural TypingInversion.

Import ScopedNotations.
Local Open Scope sumatra_scope.
Local Open Scope sessionpi_scope.
Import Lin.

(* ================================================================= *)
(* Preservation by structural congruence                             *)
(* ================================================================= *)

(** Since we define structural congruence with a single inductive, Lemmas 4 and
    5 of the benchmark become one induction over [≡]. *)

(** A typing-preserving transformation of a hole is preserved by every
    process context. *)
Lemma typing_plug_mono {n k} (C : pctx n k) (P Q : proc k) :
  (forall Ψ : ctx k, Ψ ⊢ P -> Ψ ⊢ Q) ->
  forall Δ : ctx n, Δ ⊢ C⟦P⟧ -> Δ ⊢ C⟦Q⟧.
Proof.
  intros HPQ; induction C; intros Δ Hty.
  all: try solve [dependent destruction Hty; econstructor; eauto].
  apply HPQ; exact Hty.
Qed.

(** The typing content of scope extrusion. *)
Lemma typing_scope_extrusion {n} (Δ : ctx n) P Q :
  Δ ⊢ p_par (p_res P) Q <->
  Δ ⊢ p_res (p_par P (ren_proc shift2 Q)).
Proof.
  split; intro Hty.
  - dependent destruction Hty; dependent destruction Hty1.
    eapply ht_res, ht_par with
      (Δ1 := (dual T, L) .:: (T, L) .:: Δ0)
      (Δ2 := spent (dual T) .: (spent T .: Δ2)).
    + exact Hty1.
    + unfold shift2; rewrite <- renRen_proc.
      do 2 (apply typing_weak_top; [| reflexivity]); exact Hty2.
    + sumatra_solve_join.
  - dependent destruction Hty; dependent destruction Hty.
    destruct (@typing_shift2_inv n Δ2 Q Hty2) as [HQ [HE2h HE2t]].
    assert (E : Δ1 = (dual T, L) .:: (T, L) .:: ctx_tail (ctx_tail Δ1)).
    { apply ctx_ext; intros [[i|]|].
      - reflexivity.
      - symmetry; exact (ctx_join_zero_r_at _ H HE2t).
      - symmetry; exact (ctx_join_zero_r_at _ H HE2h). }
    rewrite E in Hty1.
    eapply ht_par with
      (Δ1 := ctx_tail (ctx_tail Δ1))
      (Δ2 := ctx_tail (ctx_tail Δ2)).
    + eapply ht_res; exact Hty1.
    + exact HQ.
    + intro i; exact (H (Some (Some i))).
Qed.

Lemma preservation_scong {n} (Δ : ctx n) (P Q : proc n) :
  P ≡ Q ->
  (Δ ⊢ P <-> Δ ⊢ Q).
Proof.
  intro HC; revert Δ; induction HC; intro Δ.
  (* axioms *)
  - split; intro Hty; dependent destruction Hty;
      eapply ht_par; eauto using ctx_join_comm.
  - split; intro Hty; dependent destruction Hty.
    + dependent destruction Hty1.
      sumatra_join_reassoc.
      eapply ht_par; [ | eapply ht_par | ]; eassumption.
    + dependent destruction Hty2.
      sumatra_join_reassoc.
      eapply ht_par; [eapply ht_par | | ]; eassumption.
  - split; intro Hty.
    + dependent destruction Hty.
      dependent destruction Hty2.
      eapply typing_weak_join; eassumption.
    + eapply ht_par.
      * exact Hty.
      * apply ht_nil, ctx_zero_is_zero.
      * apply ctx_join_zero_r.
  - apply typing_scope_extrusion.
  - split; intro Hty.
    + dependent destruction Hty. dependent destruction Hty.
      eapply ht_res, ht_res, exch_pairs; exact Hty.
    + dependent destruction Hty. dependent destruction Hty.
      eapply ht_res, ht_res, exch_pairs_inv; exact Hty.
  - split; intro Hty; dependent destruction Hty.
    + eapply ht_res, exch_top.
      rewrite <- (dual_involutive T), dual_involutive in Hty.
      exact Hty.
    + eapply ht_res.
      pose proof (exch_top Hty) as H'.
      rewrite renRen_proc, swap_top_involutive, rinstId_proc in H'.
      rewrite <- (dual_involutive T), (dual_involutive (dual T)) in H'.
      exact H'.
  (* sc_refl / sc_sym / sc_trans *)
  - tauto.
  - specialize (IHHC Δ); tauto.
  - specialize (IHHC1 Δ); specialize (IHHC2 Δ); tauto.
  (* sc_cong *)
  - split; intro Hty.
    + eapply typing_plug_mono;
        [intros Ψ HP; exact (proj1 (IHHC Ψ) HP) | exact Hty].
    + eapply typing_plug_mono;
        [intros Ψ HQ; exact (proj2 (IHHC Ψ) HQ) | exact Hty].
Qed.
