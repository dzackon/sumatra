(** * Syntax of the adjoint λ-calculus

    The well-scoped de Bruijn syntax and its renaming / substitution
    infrastructure were generated with Autosubst 2 using [Syntax.sig] and then
    cleaned up for readability. Constructor names carry underscores (`ty_lolli`,
    `tm_lam`) that were added after generation, because Autosubst 2's signature
    lexer does not accept underscores. The preamble imports [core] and [fintype]
    from [Sumatra.Autosubst] so that no separate installation is needed.
    Object-language notation and the notation scope [adjointnd_scope] were also
    added by hand. *)

From Stdlib Require Import FunctionalExtensionality Relation_Definitions.
From Sumatra.Autosubst Require Import core fintype.

Declare Scope adjointnd_scope.
Delimit Scope adjointnd_scope with adjointnd.

Section Adjoint.
Variable M : Type.

(* ================================================================= *)
(* Types                                                             *)
(* ================================================================= *)

Inductive ty : Type :=
  | ty_one   : ty                  (* 1        *)
  | ty_lolli : ty -> ty -> ty      (* A ⊸ B    *)
  | ty_up    : M -> M -> ty -> ty  (* ↑[m,k] A *)
  | ty_down  : M -> M -> ty -> ty. (* ↓[m,k] A *)

Lemma congr_ty_lolli {s0 s1 t0 t1 : ty}
  (H1 : s0 = t0) (H2 : s1 = t1) : ty_lolli s0 s1 = ty_lolli t0 t1.
Proof. congruence. Qed.

Lemma congr_ty_up {s0 s1 : M} {s2 : ty} {t0 t1 : M} {t2 : ty}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ty_up s0 s1 s2 = ty_up t0 t1 t2.
Proof. congruence. Qed.

Lemma congr_ty_down {s0 s1 : M} {s2 : ty} {t0 t1 : M} {t2 : ty}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ty_down s0 s1 s2 = ty_down t0 t1 t2.
Proof. congruence. Qed.

(* ================================================================= *)
(* Terms (well-scoped de Bruijn)                                     *)
(* ================================================================= *)

Inductive tm (n : nat) : Type :=
  | tm_var     : fin n -> tm n
  | tm_lam     : ty -> tm (S n) -> tm n
  | tm_app     : tm n -> tm n -> tm n
  | tm_unit    : tm n
  | tm_letunit : tm n -> tm n -> tm n
  | tm_susp    : M -> M -> tm n -> tm n
  | tm_force   : M -> M -> tm n -> tm n
  | tm_down    : M -> M -> tm n -> tm n
  | tm_letdown : M -> tm n -> tm (S n) -> tm n.

Lemma congr_lam {m : nat} {s0 t0 : ty} {s1 t1 : tm (S m)}
  (H1 : s0 = t0) (H2 : s1 = t1) : tm_lam m s0 s1 = tm_lam m t0 t1.
Proof. congruence. Qed.

Lemma congr_app {m : nat} {s0 s1 t0 t1 : tm m}
  (H1 : s0 = t0) (H2 : s1 = t1) : tm_app m s0 s1 = tm_app m t0 t1.
Proof. congruence. Qed.

Lemma congr_unit {m : nat} : tm_unit m = tm_unit m.
Proof. reflexivity. Qed.

Lemma congr_letunit {m : nat} {s0 s1 t0 t1 : tm m}
  (H1 : s0 = t0) (H2 : s1 = t1) : tm_letunit m s0 s1 = tm_letunit m t0 t1.
Proof. congruence. Qed.

Lemma congr_susp {m : nat} {s0 s1 : M} {s2 : tm m} {t0 t1 : M} {t2 : tm m}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) :
  tm_susp m s0 s1 s2 = tm_susp m t0 t1 t2.
Proof. congruence. Qed.

Lemma congr_force {m : nat} {s0 s1 : M} {s2 : tm m} {t0 t1 : M} {t2 : tm m}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) :
  tm_force m s0 s1 s2 = tm_force m t0 t1 t2.
Proof. congruence. Qed.

Lemma congr_down {m : nat} {s0 s1 : M} {s2 : tm m} {t0 t1 : M} {t2 : tm m}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) :
  tm_down m s0 s1 s2 = tm_down m t0 t1 t2.
Proof. congruence. Qed.

Lemma congr_letdown {m : nat} {s0 : M} {s1 : tm m} {s2 : tm (S m)}
  {t0 : M} {t1 : tm m} {t2 : tm (S m)}
  (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) :
  tm_letdown m s0 s1 s2 = tm_letdown m t0 t1 t2.
Proof. congruence. Qed.

(* ================================================================= *)
(* Renaming / substitution                                           *)
(* ================================================================= *)

Definition upRen_tm_tm {m n : nat} (xi : fin m -> fin n) : fin (S m) -> fin (S n) :=
  up_ren xi.

Fixpoint ren_tm {m n : nat} (xi : fin m -> fin n) (s : tm m) : tm n :=
  match s with
  | tm_var _ x           => tm_var n (xi x)
  | tm_lam _ T e         => tm_lam n T (ren_tm (upRen_tm_tm xi) e)
  | tm_app _ e1 e2       => tm_app n (ren_tm xi e1) (ren_tm xi e2)
  | tm_unit _            => tm_unit n
  | tm_letunit _ e1 e2   => tm_letunit n (ren_tm xi e1) (ren_tm xi e2)
  | tm_susp _ a b e      => tm_susp n a b (ren_tm xi e)
  | tm_force _ a b e     => tm_force n a b (ren_tm xi e)
  | tm_down _ a b e      => tm_down n a b (ren_tm xi e)
  | tm_letdown _ a e1 e2 => tm_letdown n a (ren_tm xi e1) (ren_tm (upRen_tm_tm xi) e2)
  end.

Definition up_tm_tm {m n : nat} (sigma : fin m -> tm n) : fin (S m) -> tm (S n) :=
  scons (tm_var (S n) var_zero) (funcomp (ren_tm shift) sigma).

Fixpoint subst_tm {m n : nat} (sigma : fin m -> tm n) (s : tm m) : tm n :=
  match s with
  | tm_var _ x           => sigma x
  | tm_lam _ T e         => tm_lam n T (subst_tm (up_tm_tm sigma) e)
  | tm_app _ e1 e2       => tm_app n (subst_tm sigma e1) (subst_tm sigma e2)
  | tm_unit _            => tm_unit n
  | tm_letunit _ e1 e2   => tm_letunit n (subst_tm sigma e1) (subst_tm sigma e2)
  | tm_susp _ a b e      => tm_susp n a b (subst_tm sigma e)
  | tm_force _ a b e     => tm_force n a b (subst_tm sigma e)
  | tm_down _ a b e      => tm_down n a b (subst_tm sigma e)
  | tm_letdown _ a e1 e2 => tm_letdown n a (subst_tm sigma e1)
                                           (subst_tm (up_tm_tm sigma) e2)
  end.

Definition upId_tm_tm {m : nat} (sigma : fin m -> tm m)
  (Eq : forall x, sigma x = tm_var m x) :
  forall x, up_tm_tm sigma x = tm_var (S m) x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint idSubst_tm {m : nat} (sigma : fin m -> tm m)
  (Eq : forall x, sigma x = tm_var m x) (s : tm m) : subst_tm sigma s = s :=
  match s with
  | tm_var _ x           => Eq x
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eq) e)
  | tm_app _ e1 e2       => congr_app (idSubst_tm sigma Eq e1) (idSubst_tm sigma Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (idSubst_tm sigma Eq e1)
                                                (idSubst_tm sigma Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (idSubst_tm sigma Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (idSubst_tm sigma Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (idSubst_tm sigma Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (idSubst_tm sigma Eq e1)
                              (idSubst_tm (up_tm_tm sigma) (upId_tm_tm _ Eq) e2)
  end.

Definition upExtRen_tm_tm {m n : nat} (xi zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x :=
  fun i => match i with
           | Some x => ap shift (Eq x)
           | None   => eq_refl
           end.

Fixpoint extRen_tm {m n : nat} (xi zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) (s : tm m) : ren_tm xi s = ren_tm zeta s :=
  match s with
  | tm_var _ x           => ap (tm_var n) (Eq x)
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
                                         (upExtRen_tm_tm _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (extRen_tm xi zeta Eq e1) (extRen_tm xi zeta Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (extRen_tm xi zeta Eq e1)
                                                (extRen_tm xi zeta Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (extRen_tm xi zeta Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (extRen_tm xi zeta Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (extRen_tm xi zeta Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (extRen_tm xi zeta Eq e1)
                              (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
                                         (upExtRen_tm_tm _ _ Eq) e2)
  end.

Definition upExt_tm_tm {m n : nat} (sigma tau : fin m -> tm n)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint ext_tm {m n : nat} (sigma tau : fin m -> tm n)
  (Eq : forall x, sigma x = tau x) (s : tm m) : subst_tm sigma s = subst_tm tau s :=
  match s with
  | tm_var _ x           => Eq x
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (ext_tm (up_tm_tm sigma) (up_tm_tm tau)
                                      (upExt_tm_tm _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (ext_tm sigma tau Eq e1) (ext_tm sigma tau Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (ext_tm sigma tau Eq e1)
                                                (ext_tm sigma tau Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (ext_tm sigma tau Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (ext_tm sigma tau Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (ext_tm sigma tau Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (ext_tm sigma tau Eq e1)
                              (ext_tm (up_tm_tm sigma) (up_tm_tm tau)
                                      (upExt_tm_tm _ _ Eq) e2)
  end.

Definition up_ren_ren_tm_tm {k l m : nat} (xi : fin k -> fin l)
  (tau : fin l -> fin m) (theta : fin k -> fin m)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (upRen_tm_tm tau) (upRen_tm_tm xi) x = upRen_tm_tm theta x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l)
  (rho : fin m -> fin l) (Eq : forall x, funcomp zeta xi x = rho x) (s : tm m) :
  ren_tm zeta (ren_tm xi s) = ren_tm rho s :=
  match s with
  | tm_var _ x           => ap (tm_var l) (Eq x)
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
                                 (upRen_tm_tm rho) (up_ren_ren _ _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (compRenRen_tm xi zeta rho Eq e1)
                                      (compRenRen_tm xi zeta rho Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (compRenRen_tm xi zeta rho Eq e1)
                                                (compRenRen_tm xi zeta rho Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (compRenRen_tm xi zeta rho Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (compRenRen_tm xi zeta rho Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (compRenRen_tm xi zeta rho Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (compRenRen_tm xi zeta rho Eq e1)
                              (compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta)
                                 (upRen_tm_tm rho) (up_ren_ren _ _ _ Eq) e2)
  end.

Definition up_ren_subst_tm_tm {k l m : nat} (xi : fin k -> fin l)
  (tau : fin l -> tm m) (theta : fin k -> tm m)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint compRenSubst_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l)
  (theta : fin m -> tm l) (Eq : forall x, funcomp tau xi x = theta x) (s : tm m) :
  subst_tm tau (ren_tm xi s) = subst_tm theta s :=
  match s with
  | tm_var _ x           => Eq x
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau)
                                 (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (compRenSubst_tm xi tau theta Eq e1)
                                      (compRenSubst_tm xi tau theta Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (compRenSubst_tm xi tau theta Eq e1)
                                                (compRenSubst_tm xi tau theta Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (compRenSubst_tm xi tau theta Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (compRenSubst_tm xi tau theta Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (compRenSubst_tm xi tau theta Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (compRenSubst_tm xi tau theta Eq e1)
                              (compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau)
                                 (up_tm_tm theta) (up_ren_subst_tm_tm _ _ _ Eq) e2)
  end.

Definition up_subst_ren_tm_tm {k l m : nat} (sigma : fin k -> tm l)
  (zeta : fin l -> fin m) (theta : fin k -> tm m)
  (Eq : forall x, funcomp (ren_tm zeta) sigma x = theta x) :
  forall x, funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  fun i => match i with
           | Some x =>
               eq_trans
                 (compRenRen_tm shift (upRen_tm_tm zeta) (funcomp shift zeta)
                    (fun _ => eq_refl) (sigma x))
                 (eq_trans
                    (eq_sym (compRenRen_tm zeta shift (funcomp shift zeta)
                               (fun _ => eq_refl) (sigma x)))
                    (ap (ren_tm shift) (Eq x)))
           | None => eq_refl
           end.

Fixpoint compSubstRen_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l)
  (theta : fin m -> tm l) (Eq : forall x, funcomp (ren_tm zeta) sigma x = theta x)
  (s : tm m) : ren_tm zeta (subst_tm sigma s) = subst_tm theta s :=
  match s with
  | tm_var _ x           => Eq x
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta)
                                 (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (compSubstRen_tm sigma zeta theta Eq e1)
                                      (compSubstRen_tm sigma zeta theta Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (compSubstRen_tm sigma zeta theta Eq e1)
                                                (compSubstRen_tm sigma zeta theta Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (compSubstRen_tm sigma zeta theta Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (compSubstRen_tm sigma zeta theta Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (compSubstRen_tm sigma zeta theta Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (compSubstRen_tm sigma zeta theta Eq e1)
                              (compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta)
                                 (up_tm_tm theta) (up_subst_ren_tm_tm _ _ _ Eq) e2)
  end.

Definition up_subst_subst_tm_tm {k l m : nat} (sigma : fin k -> tm l)
  (tau : fin l -> tm m) (theta : fin k -> tm m)
  (Eq : forall x, funcomp (subst_tm tau) sigma x = theta x) :
  forall x, funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  fun i => match i with
           | Some x =>
               eq_trans
                 (compRenSubst_tm shift (up_tm_tm tau)
                    (funcomp (up_tm_tm tau) shift) (fun _ => eq_refl) (sigma x))
                 (eq_trans
                    (eq_sym (compSubstRen_tm tau shift
                               (funcomp (ren_tm shift) tau) (fun _ => eq_refl) (sigma x)))
                    (ap (ren_tm shift) (Eq x)))
           | None => eq_refl
           end.

Fixpoint compSubstSubst_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l)
  (theta : fin m -> tm l) (Eq : forall x, funcomp (subst_tm tau) sigma x = theta x)
  (s : tm m) : subst_tm tau (subst_tm sigma s) = subst_tm theta s :=
  match s with
  | tm_var _ x           => Eq x
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau)
                                 (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (compSubstSubst_tm sigma tau theta Eq e1)
                                      (compSubstSubst_tm sigma tau theta Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (compSubstSubst_tm sigma tau theta Eq e1)
                                                (compSubstSubst_tm sigma tau theta Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (compSubstSubst_tm sigma tau theta Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (compSubstSubst_tm sigma tau theta Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (compSubstSubst_tm sigma tau theta Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (compSubstSubst_tm sigma tau theta Eq e1)
                              (compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau)
                                 (up_tm_tm theta) (up_subst_subst_tm_tm _ _ _ Eq) e2)
  end.

Definition rinstInst_up_tm_tm {m n : nat} (xi : fin m -> fin n)
  (sigma : fin m -> tm n) (Eq : forall x, funcomp (tm_var n) xi x = sigma x) :
  forall x, funcomp (tm_var (S n)) (upRen_tm_tm xi) x = up_tm_tm sigma x :=
  fun i => match i with
           | Some x => ap (ren_tm shift) (Eq x)
           | None   => eq_refl
           end.

Fixpoint rinst_inst_tm {m n : nat} (xi : fin m -> fin n) (sigma : fin m -> tm n)
  (Eq : forall x, funcomp (tm_var n) xi x = sigma x) (s : tm m) :
  ren_tm xi s = subst_tm sigma s :=
  match s with
  | tm_var _ x           => Eq x
  | tm_lam _ T e         => congr_lam (eq_refl T)
                              (rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma)
                                 (rinstInst_up_tm_tm _ _ Eq) e)
  | tm_app _ e1 e2       => congr_app (rinst_inst_tm xi sigma Eq e1)
                                      (rinst_inst_tm xi sigma Eq e2)
  | tm_unit _            => congr_unit
  | tm_letunit _ e1 e2   => congr_letunit (rinst_inst_tm xi sigma Eq e1)
                                                (rinst_inst_tm xi sigma Eq e2)
  | tm_susp _ a b e      => congr_susp (eq_refl a) (eq_refl b) (rinst_inst_tm xi sigma Eq e)
  | tm_force _ a b e     => congr_force (eq_refl a) (eq_refl b) (rinst_inst_tm xi sigma Eq e)
  | tm_down _ a b e      => congr_down (eq_refl a) (eq_refl b) (rinst_inst_tm xi sigma Eq e)
  | tm_letdown _ a e1 e2 => congr_letdown (eq_refl a) (rinst_inst_tm xi sigma Eq e1)
                              (rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma)
                                 (rinstInst_up_tm_tm _ _ Eq) e2)
  end.

Lemma rinstInst_tm {m n : nat} (xi : fin m -> fin n) :
  ren_tm xi = subst_tm (funcomp (tm_var n) xi).
Proof. exact (functional_extensionality _ _ (fun x => rinst_inst_tm xi _ (fun _ => eq_refl) x)). Qed.

Lemma instId_tm {m : nat} : subst_tm (tm_var m) = @id (tm m).
Proof. exact (functional_extensionality _ _ (fun x => idSubst_tm (tm_var m) (fun _ => eq_refl) x)). Qed.

Lemma rinstId_tm {m : nat} : @ren_tm m m (@id (fin m)) = @id (tm m).
Proof. exact (eq_trans (rinstInst_tm (@id (fin m))) instId_tm). Qed.

Lemma varL_tm {m n : nat} (sigma : fin m -> tm n) :
  funcomp (subst_tm sigma) (tm_var m) = sigma.
Proof. exact (functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma varLRen_tm {m n : nat} (xi : fin m -> fin n) :
  funcomp (ren_tm xi) (tm_var m) = funcomp (tm_var n) xi.
Proof. exact (functional_extensionality _ _ (fun x => eq_refl)). Qed.

Lemma compComp_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) (s : tm m) :
  subst_tm tau (subst_tm sigma s) = subst_tm (funcomp (subst_tm tau) sigma) s.
Proof. exact (compSubstSubst_tm sigma tau _ (fun _ => eq_refl) s). Qed.

Lemma compComp'_tm {k l m : nat} (sigma : fin m -> tm k) (tau : fin k -> tm l) :
  funcomp (subst_tm tau) (subst_tm sigma) = subst_tm (funcomp (subst_tm tau) sigma).
Proof. exact (functional_extensionality _ _ (fun s => compComp_tm sigma tau s)). Qed.

Lemma compRen_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) (s : tm m) :
  ren_tm zeta (subst_tm sigma s) = subst_tm (funcomp (ren_tm zeta) sigma) s.
Proof. exact (compSubstRen_tm sigma zeta _ (fun _ => eq_refl) s). Qed.

Lemma compRen'_tm {k l m : nat} (sigma : fin m -> tm k) (zeta : fin k -> fin l) :
  funcomp (ren_tm zeta) (subst_tm sigma) = subst_tm (funcomp (ren_tm zeta) sigma).
Proof. exact (functional_extensionality _ _ (fun s => compRen_tm sigma zeta s)). Qed.

Lemma renComp_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) (s : tm m) :
  subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s.
Proof. exact (compRenSubst_tm xi tau _ (fun _ => eq_refl) s). Qed.

Lemma renComp'_tm {k l m : nat} (xi : fin m -> fin k) (tau : fin k -> tm l) :
  funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi).
Proof. exact (functional_extensionality _ _ (fun s => renComp_tm xi tau s)). Qed.

Lemma renRen_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) (s : tm m) :
  ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s.
Proof. exact (compRenRen_tm xi zeta _ (fun _ => eq_refl) s). Qed.

Lemma renRen'_tm {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l) :
  funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi).
Proof. exact (functional_extensionality _ _ (fun s => renRen_tm xi zeta s)). Qed.

(* ================================================================= *)
(* Type-class instances and notations                                *)
(* ================================================================= *)

Global Instance Subst_tm {m n : nat} : Subst1 (fin m -> tm n) (tm m) (tm n) := @subst_tm m n.
Global Instance Ren_tm   {m n : nat} : Ren1   (fin m -> fin n) (tm m) (tm n) := @ren_tm m n.
Global Instance VarInstance_tm {m : nat} : Var (fin m) (tm m) := @tm_var m.

Notation "x '__tm'" := (tm_var x) (at level 5, format "x __tm") : subst_scope.
Notation "'var'"    := (tm_var) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm)    (only printing) : subst_scope.
Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm {m n : nat} : Up_tm _ _ := @up_tm_tm m n.

Notation "s [ sigma ]" := (subst_tm sigma s) (at level 7, left associativity, only printing) : subst_scope.
Notation "[ sigma ]"   := (subst_tm sigma)   (at level 1, left associativity, only printing) : fscope.
Notation "s ⟨ xi ⟩"    := (ren_tm xi s)      (at level 7, left associativity, only printing) : subst_scope.
Notation "⟨ xi ⟩"      := (ren_tm xi)        (at level 1, left associativity, only printing) : fscope.

End Adjoint.

(* ================================================================= *)
(* Tactics                                                           *)
(* ================================================================= *)

Ltac auto_unfold :=
  repeat unfold subst1, subst2, Subst1, Subst2, ids, ren1, ren2, Ren1, Ren2,
                Subst_tm, Ren_tm, VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" :=
  repeat unfold subst1, subst2, Subst1, Subst2, ids, ren1, ren2, Ren1, Ren2,
                Subst_tm, Ren_tm, VarInstance_tm in *.

Ltac asimpl' :=
  repeat first
    [ progress rewrite ?instId_tm
    | progress rewrite ?compComp_tm
    | progress rewrite ?compComp'_tm
    | progress rewrite ?rinstId_tm
    | progress rewrite ?compRen_tm
    | progress rewrite ?compRen'_tm
    | progress rewrite ?renComp_tm
    | progress rewrite ?renComp'_tm
    | progress rewrite ?renRen_tm
    | progress rewrite ?renRen'_tm
    | progress rewrite ?varL_tm
    | progress rewrite ?varLRen_tm
    | progress (unfold up_ren, upRen_tm_tm, up_tm_tm)
    | progress (cbn [subst_tm ren_tm])
    | fsimpl ].
Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl';
               repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.
Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).
Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).

Module Extra.
  Arguments ty         {_}.
  Arguments tm         {_}.
  Arguments tm_var     {_ _}.
  Arguments tm_lam     {_ _}.
  Arguments tm_app     {_ _}.
  Arguments tm_unit    {_ _}.
  Arguments tm_letunit {_ _}.
  Arguments tm_susp    {_ _}.
  Arguments tm_force   {_ _}.
  Arguments ty_one     {_}.
  Arguments tm_down    {_ _}.
  Arguments tm_letdown {_ _}.
  Arguments ty_lolli   {_}.
  Arguments ty_up      {_}.
  Arguments ty_down    {_}.
  Arguments ren_tm     {_ _ _}.

  #[global] Hint Opaque subst_tm : rewrite.
  #[global] Hint Opaque ren_tm   : rewrite.

  Notation "T1 ⊸ T2" := (ty_lolli T1 T2)
    (at level 51, right associativity) : adjointnd_scope.
  Notation "𝟏" := ty_one : adjointnd_scope.
  Notation "'↑[' m ',' k ']' T" := (ty_up m k T)
    (at level 30) : adjointnd_scope.
  Notation "'↓[' m ',' k ']' T" := (ty_down m k T)
    (at level 30) : adjointnd_scope.

End Extra.
Export Extra.
