(** * Syntax of the linear/affine graded λ-calculus

    This case study uses the simply typed modal fragment

      A ::= 1 | A -o[k] B | box[q,k] A

    of a graded λ-calculus over an abstract type [R] of grades. The function
    space is ungraded following GrMini (Orchard-Liepelt-Eades, 2019); its bound
    variable is assigned grade one by [Typing.ht_lam]. A graded function space
    can be represented by [box[q,k] A -o[k] B].

    Both binding connectives record the *mode* at which they bind: [A -o[k] B]
    binds its argument at mode [k], and [box[q,k] A] is opened at mode [k] by
    [let box].

    Terms are well-scoped with de Bruijn indices. *)

From Stdlib Require Import FunctionalExtensionality.
From Sumatra.Autosubst Require Import core fintype.
From Sumatra Require Import Modes.

Declare Scope graded_linaff_scope.
Delimit Scope graded_linaff_scope with graded_linaff.

Section Graded.
Variable R : Type.

(* ================================================================= *)
(* Types                                                             *)
(* ================================================================= *)

Inductive ty : Type :=
  | ty_one   : ty
  | ty_lolli : ty -> LinAff.Mode -> ty -> ty
  | ty_box   : R -> LinAff.Mode -> ty -> ty.

Lemma congr_ty_lolli {s0 s1 t0 t1 : ty} {k k' : LinAff.Mode}
  (H1 : s0 = t0) (Hk : k = k') (H2 : s1 = t1) :
  ty_lolli s0 k s1 = ty_lolli t0 k' t1.
Proof. congruence. Qed.

Lemma congr_ty_box {q q' : R} {k k' : LinAff.Mode} {s t : ty}
  (Hq : q = q') (Hk : k = k') (Hs : s = t) :
  ty_box q k s = ty_box q' k' t.
Proof. congruence. Qed.

(* ================================================================= *)
(* Terms                                                             *)
(* ================================================================= *)

Inductive tm (n : nat) : Type :=
  | tm_var     : fin n -> tm n
  | tm_lam     : ty -> tm (S n) -> tm n
  | tm_app     : tm n -> tm n -> tm n
  | tm_unit    : tm n
  | tm_letunit : tm n -> tm n -> tm n
  | tm_box     : R -> tm n -> tm n
  | tm_letbox  : tm n -> tm (S n) -> tm n.

Lemma congr_lam {n} {A A' : ty} {a a' : tm (S n)}
  (HA : A = A') (Ha : a = a') : tm_lam n A a = tm_lam n A' a'.
Proof. congruence. Qed.

Lemma congr_app {n} {a b a' b' : tm n}
  (Ha : a = a') (Hb : b = b') : tm_app n a b = tm_app n a' b'.
Proof. congruence. Qed.

Lemma congr_unit {n} : tm_unit n = tm_unit n.
Proof. reflexivity. Qed.

Lemma congr_letunit {n} {a b a' b' : tm n}
  (Ha : a = a') (Hb : b = b') : tm_letunit n a b = tm_letunit n a' b'.
Proof. congruence. Qed.

Lemma congr_box {n} {q q' : R} {a a' : tm n}
  (Hq : q = q') (Ha : a = a') : tm_box n q a = tm_box n q' a'.
Proof. congruence. Qed.

Lemma congr_letbox {n} {a a' : tm n} {b b' : tm (S n)}
  (Ha : a = a') (Hb : b = b') : tm_letbox n a b = tm_letbox n a' b'.
Proof. congruence. Qed.

(* ================================================================= *)
(* Renaming and substitution                                        *)
(* ================================================================= *)

Definition upRen_tm_tm {m n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n) := up_ren xi.

Fixpoint ren_tm {m n : nat} (xi : fin m -> fin n) (a : tm m) : tm n :=
  match a with
  | tm_var _ x       => tm_var n (xi x)
  | tm_lam _ A a     => tm_lam n A (ren_tm (upRen_tm_tm xi) a)
  | tm_app _ a b     => tm_app n (ren_tm xi a) (ren_tm xi b)
  | tm_unit _        => tm_unit n
  | tm_letunit _ a b => tm_letunit n (ren_tm xi a) (ren_tm xi b)
  | tm_box _ q a     => tm_box n q (ren_tm xi a)
  | tm_letbox _ a b  => tm_letbox n (ren_tm xi a)
                                     (ren_tm (upRen_tm_tm xi) b)
  end.

Definition up_tm_tm {m n : nat} (sigma : fin m -> tm n) :
  fin (S m) -> tm (S n) :=
  scons (tm_var (S n) var_zero) (funcomp (ren_tm shift) sigma).

Fixpoint subst_tm {m n : nat} (sigma : fin m -> tm n) (a : tm m) : tm n :=
  match a with
  | tm_var _ x       => sigma x
  | tm_lam _ A a     => tm_lam n A (subst_tm (up_tm_tm sigma) a)
  | tm_app _ a b     => tm_app n (subst_tm sigma a) (subst_tm sigma b)
  | tm_unit _        => tm_unit n
  | tm_letunit _ a b => tm_letunit n (subst_tm sigma a) (subst_tm sigma b)
  | tm_box _ q a     => tm_box n q (subst_tm sigma a)
  | tm_letbox _ a b  => tm_letbox n (subst_tm sigma a)
                                     (subst_tm (up_tm_tm sigma) b)
  end.

(** Substitute for the newest variable. *)
Definition subst_top {n : nat} (b : tm n) (a : tm (S n)) : tm n :=
  @subst_tm (S n) n (scons b (tm_var n)) a.

(** Generated identity-substitution infrastructure. *)
Definition upId_tm_tm {m : nat} (sigma : fin m -> tm m)
  (Eq : forall x, sigma x = tm_var m x) :
  forall x, up_tm_tm sigma x = tm_var (S m) x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint idSubst_tm {m : nat} (sigma : fin m -> tm m)
  (Eq : forall x, sigma x = tm_var m x) (a : tm m) : subst_tm sigma a = a :=
  match a with
  | tm_var _ x       => Eq x
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eq) a)
  | tm_app _ a b     => congr_app (idSubst_tm sigma Eq a)
                                  (idSubst_tm sigma Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (idSubst_tm sigma Eq a)
                                        (idSubst_tm sigma Eq b)
  | tm_box _ q a     => congr_box (eq_refl q) (idSubst_tm sigma Eq a)
  | tm_letbox _ a b  => congr_letbox (idSubst_tm sigma Eq a)
                           (idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eq) b)
  end.

Definition upExtRen_tm_tm {m n : nat} (xi zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x :=
  fun i => match i with
           | Some x => ap shift (Eq x)
           | None   => eq_refl
           end.

Fixpoint extRen_tm {m n : nat} (xi zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) (a : tm m) : ren_tm xi a = ren_tm zeta a :=
  match a with
  | tm_var _ x       => ap (tm_var n) (Eq x)
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
                                      (upExtRen_tm_tm _ _ Eq) a)
  | tm_app _ a b     => congr_app (extRen_tm xi zeta Eq a)
                                  (extRen_tm xi zeta Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (extRen_tm xi zeta Eq a)
                                        (extRen_tm xi zeta Eq b)
  | tm_box _ q a     => congr_box (eq_refl q) (extRen_tm xi zeta Eq a)
  | tm_letbox _ a b  => congr_letbox (extRen_tm xi zeta Eq a)
                           (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
                                      (upExtRen_tm_tm _ _ Eq) b)
  end.

Definition upExt_tm_tm {m n : nat} (sigma tau : fin m -> tm n)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint ext_tm {m n : nat} (sigma tau : fin m -> tm n)
  (Eq : forall x, sigma x = tau x) (a : tm m) :
  subst_tm sigma a = subst_tm tau a :=
  match a with
  | tm_var _ x       => Eq x
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (ext_tm (up_tm_tm sigma) (up_tm_tm tau)
                                   (upExt_tm_tm _ _ Eq) a)
  | tm_app _ a b     => congr_app (ext_tm sigma tau Eq a)
                                  (ext_tm sigma tau Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (ext_tm sigma tau Eq a)
                                        (ext_tm sigma tau Eq b)
  | tm_box _ q a     => congr_box (eq_refl q) (ext_tm sigma tau Eq a)
  | tm_letbox _ a b  => congr_letbox (ext_tm sigma tau Eq a)
                           (ext_tm (up_tm_tm sigma) (up_tm_tm tau)
                                   (upExt_tm_tm _ _ Eq) b)
  end.

(* ================================================================= *)
(* Generated renaming and substitution laws                          *)
(* ================================================================= *)

Definition up_ren_ren_tm_tm {k l m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
    funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  fun i => match i with
           | Some x => ap shift (Eq x)
           | None   => eq_refl
           end.

Fixpoint compRenRen_tm {k l m : nat} (xi : fin m -> fin k)
  (zeta : fin k -> fin l) (rho : fin m -> fin l)
  (Eq : forall x, funcomp zeta xi x = rho x) (a : tm m) :
  ren_tm zeta (ren_tm xi a) = ren_tm rho a :=
  match a with
  | tm_var _ x       => ap (tm_var l) (Eq x)
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (compRenRen_tm
                              (upRen_tm_tm xi) (upRen_tm_tm zeta)
                              (upRen_tm_tm rho) (up_ren_ren_tm_tm _ _ _ Eq) a)
  | tm_app _ a b     => congr_app (compRenRen_tm xi zeta rho Eq a)
                                  (compRenRen_tm xi zeta rho Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (compRenRen_tm xi zeta rho Eq a)
                                        (compRenRen_tm xi zeta rho Eq b)
  | tm_box _ q a     => congr_box (eq_refl q)
                           (compRenRen_tm xi zeta rho Eq a)
  | tm_letbox _ a b  => congr_letbox (compRenRen_tm xi zeta rho Eq a)
                           (compRenRen_tm
                              (upRen_tm_tm xi) (upRen_tm_tm zeta)
                              (upRen_tm_tm rho) (up_ren_ren_tm_tm _ _ _ Eq) b)
  end.

Definition up_ren_subst_tm_tm {k l m : nat} (xi : fin k -> fin l)
  (tau : fin l -> tm m) (theta : fin k -> tm m)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint compRenSubst_tm {k l m : nat} (xi : fin m -> fin k)
  (tau : fin k -> tm l) (theta : fin m -> tm l)
  (Eq : forall x, funcomp tau xi x = theta x) (a : tm m) :
  subst_tm tau (ren_tm xi a) = subst_tm theta a :=
  match a with
  | tm_var _ x       => Eq x
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (compRenSubst_tm
                              (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta)
                              (up_ren_subst_tm_tm _ _ _ Eq) a)
  | tm_app _ a b     => congr_app (compRenSubst_tm xi tau theta Eq a)
                                  (compRenSubst_tm xi tau theta Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (compRenSubst_tm xi tau theta Eq a)
                                        (compRenSubst_tm xi tau theta Eq b)
  | tm_box _ q a     => congr_box (eq_refl q)
                           (compRenSubst_tm xi tau theta Eq a)
  | tm_letbox _ a b  => congr_letbox (compRenSubst_tm xi tau theta Eq a)
                           (compRenSubst_tm
                              (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta)
                              (up_ren_subst_tm_tm _ _ _ Eq) b)
  end.

Definition up_subst_ren_tm_tm {k l m : nat} (sigma : fin k -> tm l)
  (zeta : fin l -> fin m) (theta : fin k -> tm m)
  (Eq : forall x, funcomp (ren_tm zeta) sigma x = theta x) :
  forall x,
    funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  fun i => match i with
           | Some x =>
               eq_trans
                 (compRenRen_tm shift (upRen_tm_tm zeta)
                    (funcomp shift zeta) (fun _ => eq_refl) (sigma x))
                 (eq_trans
                    (eq_sym
                       (compRenRen_tm zeta shift (funcomp shift zeta)
                          (fun _ => eq_refl) (sigma x)))
                    (ap (ren_tm shift) (Eq x)))
           | None => eq_refl
           end.

Fixpoint compSubstRen_tm {k l m : nat} (sigma : fin m -> tm k)
  (zeta : fin k -> fin l) (theta : fin m -> tm l)
  (Eq : forall x, funcomp (ren_tm zeta) sigma x = theta x) (a : tm m) :
  ren_tm zeta (subst_tm sigma a) = subst_tm theta a :=
  match a with
  | tm_var _ x       => Eq x
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (compSubstRen_tm
                              (up_tm_tm sigma) (upRen_tm_tm zeta)
                              (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eq) a)
  | tm_app _ a b     => congr_app (compSubstRen_tm sigma zeta theta Eq a)
                                  (compSubstRen_tm sigma zeta theta Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (compSubstRen_tm sigma zeta theta Eq a)
                                        (compSubstRen_tm sigma zeta theta Eq b)
  | tm_box _ q a     => congr_box (eq_refl q)
                           (compSubstRen_tm sigma zeta theta Eq a)
  | tm_letbox _ a b  => congr_letbox (compSubstRen_tm sigma zeta theta Eq a)
                           (compSubstRen_tm
                              (up_tm_tm sigma) (upRen_tm_tm zeta)
                              (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eq) b)
  end.

Definition up_subst_subst_tm_tm {k l m : nat} (sigma : fin k -> tm l)
  (tau : fin l -> tm m) (theta : fin k -> tm m)
  (Eq : forall x, funcomp (subst_tm tau) sigma x = theta x) :
  forall x,
    funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  fun i => match i with
           | Some x =>
               eq_trans
                 (compRenSubst_tm shift (up_tm_tm tau)
                    (funcomp (up_tm_tm tau) shift)
                    (fun _ => eq_refl) (sigma x))
                 (eq_trans
                    (eq_sym
                       (compSubstRen_tm tau shift
                          (funcomp (ren_tm shift) tau)
                          (fun _ => eq_refl) (sigma x)))
                    (ap (ren_tm shift) (Eq x)))
           | None => eq_refl
           end.

Fixpoint compSubstSubst_tm {k l m : nat} (sigma : fin m -> tm k)
  (tau : fin k -> tm l) (theta : fin m -> tm l)
  (Eq : forall x, funcomp (subst_tm tau) sigma x = theta x) (a : tm m) :
  subst_tm tau (subst_tm sigma a) = subst_tm theta a :=
  match a with
  | tm_var _ x       => Eq x
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (compSubstSubst_tm
                              (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta)
                              (up_subst_subst_tm_tm _ _ _ Eq) a)
  | tm_app _ a b     => congr_app (compSubstSubst_tm sigma tau theta Eq a)
                                  (compSubstSubst_tm sigma tau theta Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (compSubstSubst_tm sigma tau theta Eq a)
                                        (compSubstSubst_tm sigma tau theta Eq b)
  | tm_box _ q a     => congr_box (eq_refl q)
                           (compSubstSubst_tm sigma tau theta Eq a)
  | tm_letbox _ a b  => congr_letbox (compSubstSubst_tm sigma tau theta Eq a)
                           (compSubstSubst_tm
                              (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta)
                              (up_subst_subst_tm_tm _ _ _ Eq) b)
  end.

Definition rinstInst_up_tm_tm {m n : nat} (xi : fin m -> fin n)
  (sigma : fin m -> tm n)
  (Eq : forall x, funcomp (tm_var n) xi x = sigma x) :
  forall x, funcomp (tm_var (S n)) (upRen_tm_tm xi) x = up_tm_tm sigma x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint rinst_inst_tm {m n : nat} (xi : fin m -> fin n)
  (sigma : fin m -> tm n)
  (Eq : forall x, funcomp (tm_var n) xi x = sigma x) (a : tm m) :
  ren_tm xi a = subst_tm sigma a :=
  match a with
  | tm_var _ x       => Eq x
  | tm_lam _ A a     => congr_lam (eq_refl A)
                           (rinst_inst_tm
                              (upRen_tm_tm xi) (up_tm_tm sigma)
                              (rinstInst_up_tm_tm _ _ Eq) a)
  | tm_app _ a b     => congr_app (rinst_inst_tm xi sigma Eq a)
                                  (rinst_inst_tm xi sigma Eq b)
  | tm_unit _        => congr_unit
  | tm_letunit _ a b => congr_letunit (rinst_inst_tm xi sigma Eq a)
                                        (rinst_inst_tm xi sigma Eq b)
  | tm_box _ q a     => congr_box (eq_refl q) (rinst_inst_tm xi sigma Eq a)
  | tm_letbox _ a b  => congr_letbox (rinst_inst_tm xi sigma Eq a)
                           (rinst_inst_tm
                              (upRen_tm_tm xi) (up_tm_tm sigma)
                              (rinstInst_up_tm_tm _ _ Eq) b)
  end.

Lemma rinstInst_tm {m n : nat} (xi : fin m -> fin n) :
  ren_tm xi = subst_tm (funcomp (tm_var n) xi).
Proof.
  apply functional_extensionality; intro a.
  exact (rinst_inst_tm xi _ (fun _ => eq_refl) a).
Qed.

Lemma instId_tm {m : nat} : subst_tm (tm_var m) = (fun a : tm m => a).
Proof.
  apply functional_extensionality; intro a.
  exact (idSubst_tm (tm_var m) (fun _ => eq_refl) a).
Qed.

Lemma rinstId_tm {m : nat} :
  @ren_tm m m (fun x => x) = (fun a : tm m => a).
Proof. exact (eq_trans (rinstInst_tm (fun x => x)) instId_tm). Qed.

Lemma varL_tm {m n : nat} (sigma : fin m -> tm n) :
  funcomp (subst_tm sigma) (tm_var m) = sigma.
Proof. apply functional_extensionality; intro; reflexivity. Qed.

Lemma varLRen_tm {m n : nat} (xi : fin m -> fin n) :
  funcomp (ren_tm xi) (tm_var m) = funcomp (tm_var n) xi.
Proof. apply functional_extensionality; intro; reflexivity. Qed.

Lemma compComp_tm {k l m : nat} (sigma : fin m -> tm k)
  (tau : fin k -> tm l) (a : tm m) :
  subst_tm tau (subst_tm sigma a) =
  subst_tm (funcomp (subst_tm tau) sigma) a.
Proof. exact (compSubstSubst_tm sigma tau _ (fun _ => eq_refl) a). Qed.

Lemma compComp'_tm {k l m : nat} (sigma : fin m -> tm k)
  (tau : fin k -> tm l) :
  funcomp (subst_tm tau) (subst_tm sigma) =
  subst_tm (funcomp (subst_tm tau) sigma).
Proof. apply functional_extensionality; apply compComp_tm. Qed.

Lemma compRen_tm {k l m : nat} (sigma : fin m -> tm k)
  (zeta : fin k -> fin l) (a : tm m) :
  ren_tm zeta (subst_tm sigma a) =
  subst_tm (funcomp (ren_tm zeta) sigma) a.
Proof. exact (compSubstRen_tm sigma zeta _ (fun _ => eq_refl) a). Qed.

Lemma compRen'_tm {k l m : nat} (sigma : fin m -> tm k)
  (zeta : fin k -> fin l) :
  funcomp (ren_tm zeta) (subst_tm sigma) =
  subst_tm (funcomp (ren_tm zeta) sigma).
Proof. apply functional_extensionality; apply compRen_tm. Qed.

Lemma renComp_tm {k l m : nat} (xi : fin m -> fin k)
  (tau : fin k -> tm l) (a : tm m) :
  subst_tm tau (ren_tm xi a) = subst_tm (funcomp tau xi) a.
Proof. exact (compRenSubst_tm xi tau _ (fun _ => eq_refl) a). Qed.

Lemma renComp'_tm {k l m : nat} (xi : fin m -> fin k)
  (tau : fin k -> tm l) :
  funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi).
Proof. apply functional_extensionality; apply renComp_tm. Qed.

Lemma renRen_tm {k l m : nat} (xi : fin m -> fin k)
  (zeta : fin k -> fin l) (a : tm m) :
  ren_tm zeta (ren_tm xi a) = ren_tm (funcomp zeta xi) a.
Proof. exact (compRenRen_tm xi zeta _ (fun _ => eq_refl) a). Qed.

Lemma renRen'_tm {k l m : nat} (xi : fin m -> fin k)
  (zeta : fin k -> fin l) :
  funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi).
Proof. apply functional_extensionality; apply renRen_tm. Qed.

(* ================================================================= *)
(* Notation                                                          *)
(* ================================================================= *)

End Graded.

Module Extra.
  Arguments ty       {_}.
  Arguments tm       {_}.
  Arguments tm_var   {_ _}.
  Arguments tm_lam   {_ _}.
  Arguments tm_app   {_ _}.
  Arguments tm_unit  {_ _}.
  Arguments tm_letunit {_ _}.
  Arguments tm_box   {_ _}.
  Arguments tm_letbox {_ _}.
  Arguments ty_one   {_}.
  Arguments ty_lolli {_}.
  Arguments ty_box   {_}.
  Arguments ren_tm   {_ _ _}.
  Arguments subst_tm {_ _ _}.
  Arguments subst_top {_ _}.

  Notation "A '⊸[' k ']' B" := (ty_lolli A k B)
    (at level 51, k at level 0, right associativity) : graded_linaff_scope.
  Notation "𝟏" := ty_one : graded_linaff_scope.
  Notation "'□[' q ',' k ']' A" := (ty_box q k A)
    (at level 30, q at level 0, k at level 0, A at level 30)
    : graded_linaff_scope.
End Extra.
Export Extra.
