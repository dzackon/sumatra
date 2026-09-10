(** * Context infrastructure

    Export the context infrastructure: the context datatype and its operations,
    predicates, component maps, the join relation, n-ary join families, the
    context-level facts about the canonical mode systems, renaming, and the
    availability notations. *)

From Sumatra.Context Require Export Base Predicates Maps JoinPredicates
                                    JoinAvail JoinFamily ModeInstances.
From Sumatra Require Export Join Renaming AvailNotations.

Open Scope sumatra_scope.
