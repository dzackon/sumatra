(** * Tactics

    Re-export Sumatra's automation: [Automation.Tactics] for context and
    multiplicity reasoning, and [Automation.Structural] for the object-language
    structural lemmas built on top of it. *)

From Sumatra.Automation Require Export Tactics Structural.

Open Scope sumatra_scope.
