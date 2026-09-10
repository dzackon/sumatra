(** * Contexts for the multiplicative–additive substructural λ-calculus *)

Set Implicit Arguments.

From Sumatra Require Import Modes Multiplicity Contexts.
From Sumatra.CaseStudies.Substructural Require Import Syntax.

Local Open Scope substructural_scope.

(** Assumptions pair a type with a mode drawn from an arbitrary
    [ModeSystem M] and a binary availability annotation. *)
Definition ctx {M : Type} (n : nat) : Type :=
  fctx n ty M Avail.

Arguments ctx {M} n.
