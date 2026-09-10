-- Adjoint natural deduction. The parameter "M"  becomes "Variable M : Type"
-- in the enclosing section of the generated file.

M : Type
ty : Type
tm : Type

tyone     : ty
tylolli   : ty -> ty -> ty
tyup      : M -> M -> ty -> ty
tydown    : M -> M -> ty -> ty

tmlam     : ty -> (tm -> tm) -> tm
tmapp     : tm -> tm -> tm
tmunit    : tm
tmletunit : tm -> tm -> tm
tmsusp    : M -> M -> tm -> tm
tmforce   : M -> M -> tm -> tm
tmdown    : M -> M -> tm -> tm
tmletdown : M -> tm -> (tm -> tm) -> tm
