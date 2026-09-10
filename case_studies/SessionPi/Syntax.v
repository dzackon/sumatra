(** * Syntax of the session-typed π-calculus

      Unlike the other case studies, this file was written by hand in the style
      of the Autosubst 2 output rather than generated from a [.sig] file. We 
      also include [dual] with its involution lemma, and [shift2] for the two
      names a restriction binds at once. *)

From Sumatra.Autosubst Require Import core fintype.

Declare Scope sessionpi_scope.
Delimit Scope sessionpi_scope with sessionpi.

(* ================================================================= *)
(* Session types                                                     *)
(* ================================================================= *)

Section ty.

  Inductive ty : Type :=
    | ty_wait : ty                  (* end? *)
    | ty_close : ty                 (* end! *)
    | ty_recv : ty -> ty -> ty      (* ?T.U *)
    | ty_send : ty -> ty -> ty.     (* !T.U *)

  (** No finite session type is equal to a prefix carrying itself. *)
  Lemma ty_recv_not_payload (T U : ty) : ty_recv T U <> T.
  Proof.
    revert U; induction T; intros U E; try discriminate.
    injection E as E _; exact (IHT1 _ E).
  Qed.

  Lemma ty_send_not_payload (T U : ty) : ty_send T U <> T.
  Proof.
    revert U; induction T; intros U E; try discriminate.
    injection E as E _; exact (IHT1 _ E).
  Qed.

End ty.

(** ** Duality *)

Fixpoint dual (A : ty) : ty :=
  match A with
  | ty_wait      => ty_close
  | ty_close     => ty_wait
  | ty_recv T U  => ty_send T (dual U)
  | ty_send T U  => ty_recv T (dual U)
  end.

Lemma dual_involutive (T : ty) : dual (dual T) = T.
Proof. induction T; cbn; f_equal; auto. Qed.

(* ================================================================= *)
(* Processes                                                         *)
(* ================================================================= *)

Section proc.

  (** Binding convention: [p_res P] represents [(νxy) P], binding [x] at de
      Bruijn index 1 and [y] at index 0. [p_inp c P] represents [c?y.P],
      binding the received name [y] at index 0. *)
  Inductive proc (n : nat) : Type :=
    | p_nil   : proc n                              (* 0        *)
    | p_wait  : fin n -> proc n -> proc n           (* x?.P     *)
    | p_close : fin n -> proc n -> proc n           (* x!.P     *)
    | p_inp   : fin n -> proc (S n) -> proc n       (* x?y.P    *)
    | p_out   : fin n -> fin n -> proc n -> proc n  (* x!y.P    *)
    | p_par   : proc n -> proc n -> proc n          (* P | Q    *)
    | p_res   : proc (S (S n)) -> proc n.           (* (νxy) P  *)

  Lemma congr_p_nil {m : nat} : p_nil m = p_nil m.
  Proof. congruence. Qed.

  Lemma congr_p_wait {m : nat} {s0 t0 : fin m} {s1 t1 : proc m}
    (H0 : s0 = t0) (H1 : s1 = t1) : p_wait m s0 s1 = p_wait m t0 t1.
  Proof. congruence. Qed.

  Lemma congr_p_close {m : nat} {s0 t0 : fin m} {s1 t1 : proc m}
    (H0 : s0 = t0) (H1 : s1 = t1) : p_close m s0 s1 = p_close m t0 t1.
  Proof. congruence. Qed.

  Lemma congr_p_out {m : nat} {s0 s1 t0 t1 : fin m} {s2 t2 : proc m}
    (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) :
    p_out m s0 s1 s2 = p_out m t0 t1 t2.
  Proof. congruence. Qed.

  Lemma congr_p_inp {m : nat} {s0 t0 : fin m} {s1 t1 : proc (S m)}
    (H1 : s0 = t0) (H2 : s1 = t1) : p_inp m s0 s1 = p_inp m t0 t1.
  Proof. congruence. Qed.

  Lemma congr_p_par {m : nat} {s0 s1 t0 t1 : proc m}
    (H1 : s0 = t0) (H2 : s1 = t1) : p_par m s0 s1 = p_par m t0 t1.
  Proof. congruence. Qed.

  Lemma congr_p_res {m : nat} {s0 t0 : proc (S (S m))} (H : s0 = t0) :
    p_res m s0 = p_res m t0.
  Proof. congruence. Qed.

End proc.

Arguments p_nil {n}. Arguments p_wait {n}. Arguments p_close {n}.
Arguments p_out {n}. Arguments p_inp  {n}. Arguments p_par {n}.
Arguments p_res {n}.

(* ================================================================= *)
(* Renaming                                                          *)
(* ================================================================= *)

Fixpoint ren_proc {m n : nat} (xi : fin m -> fin n) (P : proc m) : proc n :=
  match P return proc n with
  | p_nil       => p_nil
  | p_wait c P  => p_wait (xi c) (ren_proc xi P)
  | p_close c P => p_close (xi c) (ren_proc xi P)
  | p_out c y P => p_out (xi c) (xi y) (ren_proc xi P)
  | p_inp c P   => p_inp (xi c) (ren_proc (up_ren xi) P)
  | p_par P Q   => p_par (ren_proc xi P) (ren_proc xi Q)
  | p_res P     => p_res (ren_proc (up_ren (up_ren xi)) P)
  end.

(** Weakening past the two binders introduced by a restriction. *)
Definition shift2 {n : nat} : fin n -> fin (S (S n)) :=
  funcomp shift shift.

(* ================================================================= *)
(* Extensionality and functor laws for [ren_proc]                    *)
(* ================================================================= *)

Fixpoint extRen_proc {m n : nat} (xi zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) (P : proc m) : ren_proc xi P = ren_proc zeta P :=
  match P with
  | p_nil       => congr_p_nil
  | p_wait c P  => congr_p_wait (Eq c) (extRen_proc xi zeta Eq P)
  | p_close c P => congr_p_close (Eq c) (extRen_proc xi zeta Eq P)
  | p_out c y P => congr_p_out (Eq c) (Eq y) (extRen_proc xi zeta Eq P)
  | p_inp c P   => congr_p_inp (Eq c) (extRen_proc _ _ (upExtRen Eq) P)
  | p_par P Q   => congr_p_par (extRen_proc xi zeta Eq P) (extRen_proc xi zeta Eq Q)
  | p_res P     => congr_p_res (extRen_proc _ _ (upExtRen (upExtRen Eq)) P)
  end.

Local Lemma up_ren_ren_proc {k l m : nat}
  (xi : fin m -> fin k) (zeta : fin k -> fin l) (rho : fin m -> fin l)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (up_ren zeta) (up_ren xi) x = up_ren rho x.
Proof.
  intros [x|].
  - change (Some (zeta (xi x)) = Some (rho x)).
    pose proof (Eq x) as E; unfold funcomp in E. now rewrite E.
  - reflexivity.
Qed.

Fixpoint compRenRen_proc {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l)
  (rho : fin m -> fin l) (Eq : forall x, funcomp zeta xi x = rho x) (P : proc m) :
  ren_proc zeta (ren_proc xi P) = ren_proc rho P :=
  match P with
  | p_nil       => congr_p_nil
  | p_wait c P  => congr_p_wait (Eq c) (compRenRen_proc xi zeta rho Eq P)
  | p_close c P => congr_p_close (Eq c) (compRenRen_proc xi zeta rho Eq P)
  | p_out c y P => congr_p_out (Eq c) (Eq y) (compRenRen_proc xi zeta rho Eq P)
  | p_inp c P   => congr_p_inp (Eq c)
                     (compRenRen_proc _ _ _ (up_ren_ren_proc xi zeta rho Eq) P)
  | p_par P Q   => congr_p_par (compRenRen_proc xi zeta rho Eq P)
                     (compRenRen_proc xi zeta rho Eq Q)
  | p_res P     => congr_p_res
                     (compRenRen_proc _ _ _
                       (up_ren_ren_proc _ _ _
                         (up_ren_ren_proc xi zeta rho Eq)) P)
  end.

Lemma renRen_proc {k l m : nat} (xi : fin m -> fin k) (zeta : fin k -> fin l)
  (P : proc m) : ren_proc zeta (ren_proc xi P) = ren_proc (funcomp zeta xi) P.
Proof. exact (compRenRen_proc xi zeta _ (fun _ => eq_refl) P). Qed.

Lemma rinstId_proc {m : nat} (P : proc m) :
  ren_proc id P = P.
Proof.
  induction P; cbn; f_equal; try assumption.
  - transitivity (ren_proc id P); [| exact IHP].
    apply extRen_proc. intros [x|]; reflexivity.
  - transitivity (ren_proc id P); [| exact IHP].
    apply extRen_proc. intros [[x|]|]; reflexivity.
Qed.
