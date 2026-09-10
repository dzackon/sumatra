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
