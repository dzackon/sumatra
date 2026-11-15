(** * Sumatra

    Top-level interface: importing [Sumatra.All] brings the public library
    interfaces, standard instances, and automation into scope. *)

From Sumatra.Autosubst Require Export fintype.
From Sumatra Require Export
  EqDec Modes Multiplicity Semiring Contexts SemiringContext
  Substitution WeightedSubstitution Tactics.

Open Scope sumatra_scope.
