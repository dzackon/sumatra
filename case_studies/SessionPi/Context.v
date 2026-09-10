(** * Contexts for the session-typed π-calculus *)

Set Implicit Arguments.

From Sumatra.Autosubst Require Import core fintype.
From Sumatra Require Import Modes Multiplicity Contexts.
From Sumatra.CaseStudies.SessionPi Require Import Syntax.

Local Open Scope sumatra_scope.
Local Open Scope sessionpi_scope.
Import Lin.

(** Contexts: session types as resources, [Lin] modes, availability
    multiplicities. *)
Definition ctx (n : nat) : Type := fctx n ty Lin.Mode Avail.

(** Entries and their two availability states. *)
Notation sentry := (Entry ty Lin.Mode Avail).

(** Abbreviation for the sole [Lin] mode. *)
Notation "'L'" := Lin.Lin : sessionpi_scope.

Definition live  (T : ty) : sentry := (| T, L, One |).
Definition spent (T : ty) : sentry := (| T, L, Zero |).

(** Under the single linear mode no live entry can be discarded, so being
    discardable and being spent coincide. *)
Lemma entry_weak_iff_zero (e : sentry) : entry_weak e <-> e.(mult) = mzero.
Proof.
  split.
  - intro HW; destruct (mult e) eqn:Hm; [reflexivity |].
    exfalso; apply (HW ltac:(rewrite Hm; discriminate)).
  - intros Hz Hnz; exfalso; apply Hnz; exact Hz.
Qed.

Corollary ctx_weak_iff_is_zero {n} (Δ : ctx n) : ctx_weak Δ <-> ctx_is_zero Δ.
Proof. split; intros H i; apply entry_weak_iff_zero, H. Qed.
