(** * Simultaneous substitution

    Re-export the allocation judgment [subst_alloc], the splitting and composition
    laws, and the focusing, renaming, and identity operations.
    
    The quantitative, semiring-weighted counterpart is in
    [Sumatra.WeightedSubstitution]. *)

From Sumatra.Substitution Require Export Core Split Operations.

Open Scope sumatra_scope.
