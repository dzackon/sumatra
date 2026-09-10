(** * Weighted substitution

    Re-export the semiring-weighted allocation judgment from
    [Substitution.Weighted] (the quantitative counterpart of
    [Sumatra.Substitution], in which each source variable's share of the target
    context is scaled by the grade at which that variable occurs). *)

From Sumatra.Substitution Require Export Weighted.

Open Scope sumatra_scope.
