(** * Derived typing rules for the dual-mode substructural λ-calculus *)

Set Implicit Arguments.

From Sumatra.Autosubst Require Import core fintype.
From Sumatra Require Import Modes Multiplicity Contexts Tactics.
From Sumatra.CaseStudies.DualMode Require Import Syntax Context Typing.

Import ScopedNotations.
Local Open Scope dualmode_scope.

Section DerivedRules.
  Context {M : Type} `{MS : DualModeSystem M}.

  (** A singleton context types its own variable (when it is available). *)
  Lemma ctx_singleton_typing {n} (Δ : ctx n) (i : fin n) :
    (Δ i).(mult) <> mzero ->
    ctx_singleton Δ i ⊢ tm_var i : (Δ i).(res).
  Proof.
    intro Hnz.
    pose proof (avail_nonzero_one Hnz) as Hone.
    econstructor.
    - rewrite ctx_singleton_eq; now sumatra_entry_ext.
    - rewrite ctx_singleton_consume_self; apply ctx_zero_all_live.
  Qed.

End DerivedRules.
