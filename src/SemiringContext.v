(** * Semiring contexts

    Re-export the semiring context infrastructure: context scaling from
    [Context.Scaling], grade-one singletons from [Context.SemiringSingleton],
    and their interaction with renaming from [Renaming.Graded]. *)

From Sumatra.Context Require Export Scaling SemiringSingleton.
From Sumatra.Renaming Require Export Graded.

Open Scope sumatra_scope.
