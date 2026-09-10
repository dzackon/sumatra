(** * Notation specific to the {Zero, One} availability algebra *)

From Sumatra Require Import Multiplicity.
From Sumatra.Autosubst Require Import fintype.
From Sumatra.Context Require Import Base.

Import ScopedNotations.
Local Open Scope sumatra_scope.

(** Cons an available ([One]) variable [(T, m)] onto a context. *)
Notation "e .:: C" := (mk_entry (fst e) (snd e) One .: C)
  (at level 55, right associativity) : sumatra_scope.
