-- Dual-mode substructural lambda-calculus.

ty : Type
tm : Type

tybase   : ty
tyarrow  : ty -> ty -> ty
tybox    : ty -> ty

tmlam    : ty -> (tm -> tm) -> tm
tmapp    : tm -> tm -> tm
tmbox    : tm -> tm
tmletbox : tm -> (tm -> tm) -> tm
