-- Generic multiplicative-additive substructural lambda-calculus.

ty : Type
tm : Type

tybase    : ty
tylolli   : ty -> ty -> ty
tytensor  : ty -> ty -> ty
tyone     : ty
tywith    : ty -> ty -> ty
tytop     : ty
typlus    : ty -> ty -> ty
tyzero    : ty

tmlam     : ty -> (tm -> tm) -> tm
tmapp     : tm -> tm -> tm
tmpair    : tm -> tm -> tm
tmletpair : tm -> (tm -> tm -> tm) -> tm
tmunit    : tm
tmletunit : tm -> tm -> tm
tmwith    : tm -> tm -> tm
tmfst     : tm -> tm
tmsnd     : tm -> tm
tmtop     : tm
tminl     : ty -> tm -> tm
tminr     : ty -> tm -> tm
tmcase    : tm -> (tm -> tm) -> (tm -> tm) -> tm
tmabort   : ty -> tm -> tm
