-- Graded linear/affine lambda-calculus. The parameter "R" (grades) becomes
-- "Variable R : Type"; "M" becomes the library's LinAff.Mode.

R : Type
M : Type
ty : Type
tm : Type

tyone     : ty
tylolli   : ty -> M -> ty -> ty
tybox     : R -> M -> ty -> ty

tmlam     : ty -> (tm -> tm) -> tm
tmapp     : tm -> tm -> tm
tmunit    : tm
tmletunit : tm -> tm -> tm
tmbox     : R -> tm -> tm
tmletbox  : tm -> (tm -> tm) -> tm
