(** * Syntax of the multiplicative-additive substructural λ-calculus

    The well-scoped de Bruijn syntax and its renaming / substitution
    infrastructure were generated with Autosubst 2 using [Syntax.sig] and then
    cleaned up for readability. Constructor names carry underscores (`ty_lolli`,
    `tm_lam`) that were added after generation, because Autosubst 2's signature
    lexer does not accept underscores. The preamble imports [core] and [fintype]
    from [Sumatra.Autosubst] so that no separate installation is needed.
    Object-language notation and the notation scope [substructural_scope] were
    also added by hand. *)

From Stdlib Require Import FunctionalExtensionality Morphisms.
From Sumatra.Autosubst Require Import core fintype.

Declare Scope substructural_scope.
Delimit Scope substructural_scope with substructural.

Section ty.
Inductive ty : Type :=
| ty_base   : ty
| ty_lolli  : ty -> ty -> ty
| ty_tensor : ty -> ty -> ty
| ty_one    : ty
| ty_with   : ty -> ty -> ty
| ty_top    : ty
| ty_plus   : ty -> ty -> ty
| ty_zero   : ty.

Lemma congr_lolli {s0 s1 t0 t1 : ty} (H1 : s0 = t0) (H2 : s1 = t1) :
  ty_lolli s0 s1 = ty_lolli t0 t1.
Proof. congruence. Qed.

Lemma congr_tensor {s0 s1 t0 t1 : ty} (H1 : s0 = t0) (H2 : s1 = t1) :
  ty_tensor s0 s1 = ty_tensor t0 t1.
Proof. congruence. Qed.

Lemma congr_one : ty_one = ty_one.
Proof. congruence. Qed.

Lemma congr_with {s0 s1 t0 t1 : ty} (H1 : s0 = t0) (H2 : s1 = t1) :
  ty_with s0 s1 = ty_with t0 t1.
Proof. congruence. Qed.

Lemma congr_plus {s0 s1 t0 t1 : ty} (H1 : s0 = t0) (H2 : s1 = t1) :
  ty_plus s0 s1 = ty_plus t0 t1.
Proof. congruence. Qed.

End ty.

Section tm.
Inductive tm (n : nat) : Type :=
| tm_var     : fin n -> tm n
| tm_lam     : ty -> tm (S n) -> tm n
| tm_app     : tm n -> tm n -> tm n
| tm_pair    : tm n -> tm n -> tm n
| tm_letpair : tm n -> tm (S (S n)) -> tm n
| tm_unit    : tm n
| tm_letunit : tm n -> tm n -> tm n
| tm_with    : tm n -> tm n -> tm n
| tm_fst     : tm n -> tm n
| tm_snd     : tm n -> tm n
| tm_top     : tm n
| tm_inl     : ty -> tm n -> tm n
| tm_inr     : ty -> tm n -> tm n
| tm_case    : tm n -> tm (S n) -> tm (S n) -> tm n
| tm_abort   : ty -> tm n -> tm n.

Lemma congr_tm_lam {m : nat} {s0 t0 : ty} {s1 t1 : tm (S m)}
  (H1 : s0 = t0) (H2 : s1 = t1) : tm_lam m s0 s1 = tm_lam m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_app {m : nat} {s0 s1 t0 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_app m s0 s1 = tm_app m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_pair {m : nat} {s0 s1 t0 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_pair m s0 s1 = tm_pair m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_letpair {m : nat} {s0 t0 : tm m} {s1 t1 : tm (S (S m))} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_letpair m s0 s1 = tm_letpair m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_unit {m : nat} : tm_unit m = tm_unit m.
Proof. congruence. Qed.

Lemma congr_tm_letunit {m : nat} {s0 s1 t0 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_letunit m s0 s1 = tm_letunit m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_with {m : nat} {s0 s1 t0 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_with m s0 s1 = tm_with m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_fst {m : nat} {s0 t0 : tm m} (H1 : s0 = t0) : tm_fst m s0 = tm_fst m t0.
Proof. congruence. Qed.

Lemma congr_tm_snd {m : nat} {s0 t0 : tm m} (H1 : s0 = t0) : tm_snd m s0 = tm_snd m t0.
Proof. congruence. Qed.

Lemma congr_tm_top {m : nat} : tm_top m = tm_top m.
Proof. congruence. Qed.

Lemma congr_tm_inl {m : nat} {s0 t0 : ty} {s1 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_inl m s0 s1 = tm_inl m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_inr {m : nat} {s0 t0 : ty} {s1 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_inr m s0 s1 = tm_inr m t0 t1.
Proof. congruence. Qed.

Lemma congr_tm_case {m : nat} {s0 t0 : tm m} {s1 s2 t1 t2 : tm (S m)}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : tm_case m s0 s1 s2 = tm_case m t0 t1 t2.
Proof. congruence. Qed.

Lemma congr_tm_abort {m : nat} {s0 t0 : ty} {s1 t1 : tm m} (H1 : s0 = t0) (H2 : s1 = t1) :
  tm_abort m s0 s1 = tm_abort m t0 t1.
Proof. congruence. Qed.

Definition upRen_tm_tm {m n : nat} (xi : fin m -> fin n) : fin (S m) -> fin (S n) :=
  (up_ren) xi.

Fixpoint ren_tm {m n : nat} (xi : fin m -> fin n) (t : tm m) : tm n :=
  match t return tm n with
  | tm_var _ x         => tm_var n (xi x)
  | tm_lam _ A t       => tm_lam n A (ren_tm (upRen_tm_tm xi) t)
  | tm_app _ t1 t2     => tm_app n (ren_tm xi t1) (ren_tm xi t2)
  | tm_pair _ t1 t2    => tm_pair n (ren_tm xi t1) (ren_tm xi t2)
  | tm_letpair _ t1 t2 =>
      tm_letpair n
        (ren_tm xi t1) (ren_tm (upRen_tm_tm (upRen_tm_tm xi)) t2)
  | tm_unit _          => tm_unit n
  | tm_letunit _ t1 t2 => tm_letunit n (ren_tm xi t1) (ren_tm xi t2)
  | tm_with _ t1 t2    => tm_with n (ren_tm xi t1) (ren_tm xi t2)
  | tm_fst _ t         =>  tm_fst n (ren_tm xi t)
  | tm_snd _ t         => tm_snd n (ren_tm xi t)
  | tm_top _           => tm_top n
  | tm_inl _ A t       => tm_inl n A (ren_tm xi t)
  | tm_inr _ A t       => tm_inr n A (ren_tm xi t)
  | tm_case _ t1 t2 t3 =>
      tm_case n
        (ren_tm xi t1)  (ren_tm (upRen_tm_tm xi) t2) (ren_tm (upRen_tm_tm xi) t3)
  | tm_abort _ A t     => tm_abort n A (ren_tm xi t)
  end.

Definition up_tm_tm {m n : nat} (sigma : fin m -> tm n) : fin (S m) -> tm (S n) :=
 (scons) ((tm_var (S n)) var_zero) (funcomp (ren_tm shift) sigma).

Fixpoint subst_tm {m n : nat} (sigma : fin m -> tm n) (t : tm m) : tm n :=
  match t return tm n with
  | tm_var _ x         => sigma x
  | tm_lam _ A t       =>
      tm_lam n A (subst_tm (up_tm_tm sigma) t)
  | tm_app _ t1 t2     =>
      tm_app n (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_pair _ t1 t2    =>
      tm_pair n (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_letpair _ t1 t2 =>
      tm_letpair n
        (subst_tm sigma t1)
        (subst_tm (up_tm_tm (up_tm_tm sigma)) t2)
  | tm_unit _          => tm_unit n
  | tm_letunit _ t1 t2 => tm_letunit n (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_with _ t1 t2    => tm_with n (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_fst _ t         => tm_fst n (subst_tm sigma t)
  | tm_snd _ t         => tm_snd n (subst_tm sigma t)
  | tm_top _           => tm_top n
  | tm_inl _ A t       => tm_inl n A (subst_tm sigma t)
  | tm_inr _ A t       => tm_inr n A (subst_tm sigma t)
  | tm_case _ t1 t2 t3 =>
      tm_case n
        (subst_tm sigma t1)
        (subst_tm (up_tm_tm sigma) t2)
        (subst_tm (up_tm_tm sigma) t3)
  | tm_abort _ A t     => tm_abort n A (subst_tm sigma t)
  end.

Definition upId_tm_tm {m : nat} (sigma : fin m -> tm m) (Eq : forall x, sigma x = (tm_var m) x) :
  forall x, (up_tm_tm sigma) x = (tm_var (S m)) x :=
  fun n => match n with
  | Some fn => ap (ren_tm shift) (Eq fn)
  | None => eq_refl
  end.

Fixpoint idSubst_tm {m : nat} (sigma : fin m -> tm m) (Eqtm : forall x, sigma x = (tm_var m) x) (s : tm m) :
  subst_tm sigma s = s :=
   match s return subst_tm sigma s = s with
    | tm_var _ s         => Eqtm s
    | tm_lam _ s0 s1     => congr_tm_lam (eq_refl s0) ((idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eqtm)) s1)
    | tm_app _ s0 s1     => congr_tm_app ((idSubst_tm sigma Eqtm) s0) ((idSubst_tm sigma Eqtm) s1)
    | tm_pair _ s0 s1    => congr_tm_pair ((idSubst_tm sigma Eqtm) s0) ((idSubst_tm sigma Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((idSubst_tm sigma Eqtm) s0)
        ((idSubst_tm (up_tm_tm (up_tm_tm sigma)) (upId_tm_tm _ (upId_tm_tm _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 => congr_tm_letunit ((idSubst_tm sigma Eqtm) s0) ((idSubst_tm sigma Eqtm) s1)
    | tm_with _ s0 s1    => congr_tm_with ((idSubst_tm sigma Eqtm) s0) ((idSubst_tm sigma Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((idSubst_tm sigma Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((idSubst_tm sigma Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((idSubst_tm sigma Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((idSubst_tm sigma Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((idSubst_tm sigma Eqtm) s0) ((idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eqtm)) s1)
        ((idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((idSubst_tm sigma Eqtm) s1)
    end.

Definition upExtRen_tm_tm {m n : nat} (xi zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fn => ap shift (Eq fn)
  | None => eq_refl
  end.

Fixpoint extRen_tm {m n : nat} (xi zeta : fin m -> fin n) (Eqtm : forall x, xi x = zeta x) (s : tm m) :
  ren_tm xi s = ren_tm zeta s :=
   match s return ren_tm xi s = ren_tm zeta s with
    | tm_var _ s         => ap (tm_var n) (Eqtm s)
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm _ _ Eqtm)) s1)
    | tm_app _ s0 s1     => congr_tm_app ((extRen_tm xi zeta Eqtm) s0) ((extRen_tm xi zeta Eqtm) s1)
    | tm_pair _ s0 s1    => congr_tm_pair ((extRen_tm xi zeta Eqtm) s0) ((extRen_tm xi zeta Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((extRen_tm xi zeta Eqtm) s0)
        ((extRen_tm (upRen_tm_tm (upRen_tm_tm xi)) (upRen_tm_tm (upRen_tm_tm zeta))
                    (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 => congr_tm_letunit ((extRen_tm xi zeta Eqtm) s0) ((extRen_tm xi zeta Eqtm) s1)
    | tm_with _ s0 s1    => congr_tm_with ((extRen_tm xi zeta Eqtm) s0) ((extRen_tm xi zeta Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((extRen_tm xi zeta Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((extRen_tm xi zeta Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((extRen_tm xi zeta Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((extRen_tm xi zeta Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((extRen_tm xi zeta Eqtm) s0)
        ((extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm _ _ Eqtm)) s1)
        ((extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((extRen_tm xi zeta Eqtm) s1)
    end.

Definition upExt_tm_tm {m n : nat} (sigma tau : fin m -> tm n) (Eq : forall x, sigma x = tau x) :
  forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fn => ap (ren_tm shift) (Eq fn)
  | None => eq_refl
  end.

Fixpoint ext_tm {m n : nat} (sigma tau : fin m -> tm n) (Eqtm : forall x, sigma x = tau x) (s : tm m) :
  subst_tm sigma s = subst_tm tau s :=
    match s return subst_tm sigma s = subst_tm tau s with
    | tm_var _ s         => Eqtm s
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm _ _ Eqtm)) s1)
    | tm_app _ s0 s1     => congr_tm_app ((ext_tm sigma tau Eqtm) s0) ((ext_tm sigma tau Eqtm) s1)
    | tm_pair _ s0 s1    => congr_tm_pair ((ext_tm sigma tau Eqtm) s0) ((ext_tm sigma tau Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((ext_tm sigma tau Eqtm) s0)
        ((ext_tm (up_tm_tm (up_tm_tm sigma)) (up_tm_tm (up_tm_tm tau))
                 (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 => congr_tm_letunit ((ext_tm sigma tau Eqtm) s0) ((ext_tm sigma tau Eqtm) s1)
    | tm_with _ s0 s1    => congr_tm_with ((ext_tm sigma tau Eqtm) s0) ((ext_tm sigma tau Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((ext_tm sigma tau Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((ext_tm sigma tau Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((ext_tm sigma tau Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((ext_tm sigma tau Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((ext_tm sigma tau Eqtm) s0)
        ((ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm _ _ Eqtm)) s1)
        ((ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((ext_tm sigma tau Eqtm) s1)
    end.

Definition up_ren_ren_tm_tm {k l m : nat} (xi : fin k -> fin l) (tau : fin l -> fin m) (theta : fin k -> fin m)
  (Eq : forall x, (funcomp tau xi) x = theta x) :
  forall x, (funcomp (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) (rho : fin m -> fin l)
  (Eqtm : forall x, (funcomp zeta xi) x = rho x) (s : tm m) :
  ren_tm zeta (ren_tm xi s) = ren_tm rho s :=
    match s return ren_tm zeta (ren_tm xi s) = ren_tm rho s with
    | tm_var _ s         => ap (tm_var l) (Eqtm s)
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho) (up_ren_ren _ _ _ Eqtm)) s1)
    | tm_app _ s0 s1     =>
      congr_tm_app ((compRenRen_tm xi zeta rho Eqtm) s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | tm_pair _ s0 s1    =>
      congr_tm_pair ((compRenRen_tm xi zeta rho Eqtm) s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((compRenRen_tm xi zeta rho Eqtm) s0)
        ((compRenRen_tm (upRen_tm_tm (upRen_tm_tm xi)) (upRen_tm_tm (upRen_tm_tm zeta))
                        (upRen_tm_tm (upRen_tm_tm rho)) (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 =>
      congr_tm_letunit ((compRenRen_tm xi zeta rho Eqtm) s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | tm_with _ s0 s1    =>
      congr_tm_with ((compRenRen_tm xi zeta rho Eqtm) s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((compRenRen_tm xi zeta rho Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((compRenRen_tm xi zeta rho Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((compRenRen_tm xi zeta rho Eqtm) s0)
        ((compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho) (up_ren_ren _ _ _ Eqtm)) s1)
        ((compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho) (up_ren_ren _ _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((compRenRen_tm xi zeta rho Eqtm) s1)
    end.

Definition up_ren_subst_tm_tm {k l m : nat} (xi : fin k -> fin l) (tau : fin l -> tm m) (theta : fin k -> tm m)
  (Eq : forall x, (funcomp tau xi) x = theta x) :
  forall x, (funcomp (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fn => ap (ren_tm shift) (Eq fn)
  | None => eq_refl
  end.

Fixpoint compRenSubst_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) (theta : fin m -> tm l)
  (Eqtm : forall x, (funcomp tau xi) x = theta x) (s : tm m) : subst_tm tau (ren_tm xi s) = subst_tm theta s :=
    match s return subst_tm tau (ren_tm xi s) = subst_tm theta s with
    | tm_var _ s         => Eqtm s
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eqtm)) s1)
    | tm_app _ s0 s1     =>
      congr_tm_app ((compRenSubst_tm xi tau theta Eqtm) s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | tm_pair _ s0 s1    =>
      congr_tm_pair ((compRenSubst_tm xi tau theta Eqtm) s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((compRenSubst_tm xi tau theta Eqtm) s0)
        ((compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xi)) (up_tm_tm (up_tm_tm tau)) (up_tm_tm (up_tm_tm theta))
                          (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 =>
      congr_tm_letunit ((compRenSubst_tm xi tau theta Eqtm) s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | tm_with _ s0 s1    =>
      congr_tm_with ((compRenSubst_tm xi tau theta Eqtm) s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((compRenSubst_tm xi tau theta Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((compRenSubst_tm xi tau theta Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((compRenSubst_tm xi tau theta Eqtm) s0)
        ((compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eqtm)) s1)
        ((compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((compRenSubst_tm xi tau theta Eqtm) s1)
    end.

Definition up_subst_ren_tm_tm {k l m : nat}
  (sigma : fin k -> tm l) (zeta : fin l -> fin m) (theta : fin k -> tm m)
  (Eq : forall x, (funcomp (ren_tm zeta) sigma) x = theta x) :
  forall x, (funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fn =>
    eq_trans
      (compRenRen_tm shift (upRen_tm_tm zeta) (funcomp shift zeta) (fun _ => eq_refl) (sigma fn))
      (eq_trans (eq_sym (compRenRen_tm zeta shift (funcomp shift zeta) (fun _ => eq_refl) (sigma fn)))
                (ap (ren_tm shift) (Eq fn)))
  | None => eq_refl
  end.

Fixpoint compSubstRen_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) (theta : fin m -> tm l)
  (Eqtm : forall x, (funcomp (ren_tm zeta) sigma) x = theta x) (s : tm m) :
  ren_tm zeta (subst_tm sigma s) = subst_tm theta s :=
    match s return ren_tm zeta (subst_tm sigma s) = subst_tm theta s with
    | tm_var _ s         => Eqtm s
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eqtm)) s1)
    | tm_app _ s0 s1     =>
      congr_tm_app ((compSubstRen_tm sigma zeta theta Eqtm) s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | tm_pair _ s0 s1    =>
      congr_tm_pair ((compSubstRen_tm sigma zeta theta Eqtm) s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((compSubstRen_tm sigma zeta theta Eqtm) s0)
        ((compSubstRen_tm (up_tm_tm (up_tm_tm sigma)) (upRen_tm_tm (upRen_tm_tm zeta)) (up_tm_tm (up_tm_tm theta))
                          (up_subst_ren_tm_tm _ _ _ (up_subst_ren_tm_tm _ _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 =>
      congr_tm_letunit ((compSubstRen_tm sigma zeta theta Eqtm) s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | tm_with _ s0 s1    =>
      congr_tm_with
        ((compSubstRen_tm sigma zeta theta Eqtm) s0)
        ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((compSubstRen_tm sigma zeta theta Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((compSubstRen_tm sigma zeta theta Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((compSubstRen_tm sigma zeta theta Eqtm) s0)
        ((compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eqtm)) s1)
        ((compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((compSubstRen_tm sigma zeta theta Eqtm) s1)
    end.

Definition up_subst_subst_tm_tm {k l m : nat}
  (sigma : fin k -> tm l) (tau : fin l -> tm m) (theta : fin k -> tm m)
  (Eq : forall x, (funcomp (subst_tm tau) sigma) x = theta x) :
  forall x, (funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fn =>
    eq_trans
      (compRenSubst_tm shift (up_tm_tm tau) (funcomp (up_tm_tm tau) shift) (fun _ => eq_refl) (sigma fn))
      (eq_trans (eq_sym (compSubstRen_tm tau shift (funcomp (ren_tm shift) tau) (fun _ => eq_refl) (sigma fn)))
                (ap (ren_tm shift) (Eq fn)))
  | None => eq_refl
  end.

Fixpoint compSubstSubst_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) (theta : fin m -> tm l)
  (Eqtm : forall x, (funcomp (subst_tm tau) sigma) x = theta x) (s : tm m) :
  subst_tm tau (subst_tm sigma s) = subst_tm theta s :=
    match s return subst_tm tau (subst_tm sigma s) = subst_tm theta s with
    | tm_var _ s         => Eqtm s
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eqtm)) s1)
    | tm_app _ s0 s1     =>
      congr_tm_app ((compSubstSubst_tm sigma tau theta Eqtm) s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | tm_pair _ s0 s1    =>
      congr_tm_pair ((compSubstSubst_tm sigma tau theta Eqtm) s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((compSubstSubst_tm sigma tau theta Eqtm) s0)
        ((compSubstSubst_tm (up_tm_tm (up_tm_tm sigma)) (up_tm_tm (up_tm_tm tau)) (up_tm_tm (up_tm_tm theta))
                            (up_subst_subst_tm_tm _ _ _ (up_subst_subst_tm_tm _ _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 =>
      congr_tm_letunit ((compSubstSubst_tm sigma tau theta Eqtm) s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | tm_with _ s0 s1    =>
      congr_tm_with ((compSubstSubst_tm sigma tau theta Eqtm) s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((compSubstSubst_tm sigma tau theta Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((compSubstSubst_tm sigma tau theta Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((compSubstSubst_tm sigma tau theta Eqtm) s0)
        ((compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eqtm)) s1)
        ((compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((compSubstSubst_tm sigma tau theta Eqtm) s1)
    end.

Definition rinstInst_up_tm_tm {m n : nat} (xi : fin m -> fin n) (sigma : fin m -> tm n)
  (Eq : forall x, (funcomp (tm_var n) xi) x = sigma x) :
  forall x, (funcomp (tm_var (S n)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fn => ap (ren_tm shift) (Eq fn)
  | None => eq_refl
  end.

Fixpoint rinst_inst_tm {m n : nat} (xi : fin m -> fin n) (sigma : fin m -> tm n)
  (Eqtm : forall x, (funcomp (tm_var n) xi) x = sigma x) (s : tm m) : ren_tm xi s = subst_tm sigma s :=
   match s return ren_tm xi s = subst_tm sigma s with
    | tm_var _ s         => Eqtm s
    | tm_lam _ s0 s1     =>
      congr_tm_lam
        (eq_refl s0)
        ((rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm _ _ Eqtm)) s1)
    | tm_app _ s0 s1     => congr_tm_app ((rinst_inst_tm xi sigma Eqtm) s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | tm_pair _ s0 s1    => congr_tm_pair ((rinst_inst_tm xi sigma Eqtm) s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | tm_letpair _ s0 s1 =>
      congr_tm_letpair
        ((rinst_inst_tm xi sigma Eqtm) s0)
        ((rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xi)) (up_tm_tm (up_tm_tm sigma))
                        (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eqtm))) s1)
    | tm_unit _          => congr_tm_unit
    | tm_letunit _ s0 s1 => congr_tm_letunit ((rinst_inst_tm xi sigma Eqtm) s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | tm_with _ s0 s1    => congr_tm_with ((rinst_inst_tm xi sigma Eqtm) s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | tm_fst _ s0        => congr_tm_fst ((rinst_inst_tm xi sigma Eqtm) s0)
    | tm_snd _ s0        => congr_tm_snd ((rinst_inst_tm xi sigma Eqtm) s0)
    | tm_top _           => congr_tm_top
    | tm_inl _ s0 s1     => congr_tm_inl (eq_refl s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | tm_inr _ s0 s1     => congr_tm_inr (eq_refl s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    | tm_case _ s0 s1 s2 =>
      congr_tm_case
        ((rinst_inst_tm xi sigma Eqtm) s0)
        ((rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm _ _ Eqtm)) s1)
        ((rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm _ _ Eqtm)) s2)
    | tm_abort _ s0 s1   => congr_tm_abort (eq_refl s0) ((rinst_inst_tm xi sigma Eqtm) s1)
    end.

Lemma rinstInst_tm {m n : nat} (xi : fin m -> fin n) : ren_tm xi = subst_tm (funcomp (tm_var n) xi).
Proof. exact ((functional_extensionality _ _) (fun x => rinst_inst_tm xi _ (fun _ => eq_refl) x)). Qed.

Lemma instId_tm {m : nat} : subst_tm (tm_var m) = id.
Proof. exact ((functional_extensionality _ _) (fun x => idSubst_tm (tm_var m) (fun _ => eq_refl) (id x))). Qed.

Lemma rinstId_tm {m : nat} : @ren_tm m m id = id.
Proof. exact (eq_trans (rinstInst_tm (id _)) instId_tm). Qed.

Lemma varL_tm {m n : nat} (sigma : fin m -> tm n) : funcomp (subst_tm sigma) (tm_var m) = sigma.
Proof. exact ((functional_extensionality _ _) (fun _ => eq_refl)). Qed.

Lemma varLRen_tm {m n : nat} (xi : fin m -> fin n) :
  funcomp (ren_tm xi) (tm_var m) = funcomp (tm_var n) xi.
Proof. exact ((functional_extensionality _ _) (fun _ => eq_refl)). Qed.

Lemma compComp_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) (s : tm m) :
  subst_tm tau (subst_tm sigma s) = subst_tm (funcomp (subst_tm tau) sigma) s.
Proof. exact (compSubstSubst_tm sigma tau _ (fun _ => eq_refl) s). Qed.

Lemma compComp'_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) :
  funcomp (subst_tm tau) (subst_tm sigma) = subst_tm (funcomp (subst_tm tau) sigma).
Proof. exact ((functional_extensionality _ _) (fun n => compComp_tm sigma tau n)). Qed.

Lemma compRen_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) (s : tm m) :
  ren_tm zeta (subst_tm sigma s) = subst_tm (funcomp (ren_tm zeta) sigma) s.
Proof. exact (compSubstRen_tm sigma zeta _ (fun _ => eq_refl) s). Qed.

Lemma compRen'_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) :
  funcomp (ren_tm zeta) (subst_tm sigma) = subst_tm (funcomp (ren_tm zeta) sigma).
Proof. exact ((functional_extensionality _ _) (fun n => compRen_tm sigma zeta n)). Qed.

Lemma renComp_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) (s : tm m) :
  subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s.
Proof. exact (compRenSubst_tm xi tau _ (fun _ => eq_refl) s). Qed.

Lemma renComp'_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) :
  funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi).
Proof. exact ((functional_extensionality _ _) (fun n => renComp_tm xi tau n)). Qed.

Lemma renRen_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) (s : tm m) :
  ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s.
Proof. exact (compRenRen_tm xi zeta _ (fun _ => eq_refl) s). Qed.

Lemma renRen'_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) :
  funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi).
Proof. exact ((functional_extensionality _ _) (fun n => renRen_tm xi zeta n)). Qed.

End tm.

Global Instance Subst_tm {m n : nat} : Subst1 (fin m -> tm n)  (tm m) (tm n) := @subst_tm m n.
Global Instance Ren_tm   {m n : nat} : Ren1   (fin m -> fin n) (tm m) (tm n) := @ren_tm m n.
Global Instance VarInstance_tm {m : nat} : Var (fin m) (tm m) := @tm_var m.

Notation "x '__tm'" := (tm_var x) (at level 5, format "x __tm")     : subst_scope.
(* Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
                       (at level 5, only printing, format "x __tm") : subst_scope. *)
Notation "'var'"    := (tm_var) (only printing, at level 1)         : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm)    (only printing) : subst_scope.
Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm {m n : nat} : Up_tm _ _ := @up_tm_tm m n.

Notation "s [ sigma ]" := (subst_tm sigma s) (at level 7, left associativity, only printing) : subst_scope.
Notation "[ sigma ]"   := (subst_tm sigma)   (at level 1, left associativity, only printing) : fscope.
Notation "s ⟨ xi ⟩"    := (ren_tm xi s)      (at level 7, left associativity, only printing) : subst_scope.
Notation "⟨ xi ⟩"      := (ren_tm xi)        (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1, subst2, Subst1, Subst2, ids,
  ren1, ren2, Ren1, Ren2, Subst_tm, Ren_tm, VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" :=
  repeat unfold subst1, subst2, Subst1, Subst2, ids,
    ren1, ren2, Ren1, Ren2, Subst_tm, Ren_tm, VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm | progress rewrite ?compComp_tm
  | progress rewrite ?compComp'_tm   | progress rewrite ?rinstId_tm | progress rewrite ?compRen_tm
  | progress rewrite ?compRen'_tm    | progress rewrite ?renComp_tm | progress rewrite ?renComp'_tm
  | progress rewrite ?renRen_tm      | progress rewrite ?renRen'_tm | progress rewrite ?varL_tm
  | progress rewrite ?varLRen_tm     | progress (unfold up_ren, upRen_tm_tm, up_tm_tm)
  | progress (cbn [subst_tm ren_tm]) | fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.
Tactic Notation "auto_case"          := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first
  [ progress rewrite ?instId_tm    in * | progress rewrite ?compComp_tm in *
  | progress rewrite ?compComp'_tm in * | progress rewrite ?rinstId_tm  in *
  | progress rewrite ?compRen_tm   in * | progress rewrite ?compRen'_tm in *
  | progress rewrite ?renComp_tm   in * | progress rewrite ?renComp'_tm in *
  | progress rewrite ?renRen_tm    in * | progress rewrite ?renRen'_tm  in *
  | progress rewrite ?varL_tm      in * | progress rewrite ?varLRen_tm  in *
  | progress (unfold up_ren, upRen_tm_tm, up_tm_tm in *)
  | progress (cbn [subst_tm ren_tm] in *)].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).
Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).

Module Extra.
  Arguments tm_var   {n}.
  Arguments tm_lam   {n}.
  Arguments tm_app   {n}.
  Arguments tm_pair  {n}.
  Arguments tm_letpair {n}.
  Arguments tm_unit    {n}.
  Arguments tm_letunit {n}.
  Arguments tm_with  {n}.
  Arguments tm_fst   {n}.
  Arguments tm_snd   {n}.
  Arguments tm_top   {n}.
  Arguments tm_inl   {n}.
  Arguments tm_inr   {n}.
  Arguments tm_case  {n}.
  Arguments tm_abort {n}.
  Arguments ren_tm   {m n}.
  Arguments subst_tm {m n}.

  Notation "𝟏" := ty_one : substructural_scope.
  Notation "𝟎" := ty_zero : substructural_scope.
  Notation "⊤" := ty_top : substructural_scope.
  Notation "A ⊸ B" := (ty_lolli A B)
    (at level 51, right associativity) : substructural_scope.
  Notation "A ⊗ B" := (ty_tensor A B)
    (at level 41, right associativity) : substructural_scope.
  Notation "A & B" := (ty_with A B)
    (at level 42, right associativity) : substructural_scope.
  Notation "A ⊕ B" := (ty_plus A B)
    (at level 43, right associativity) : substructural_scope.

End Extra.
Export Extra.
