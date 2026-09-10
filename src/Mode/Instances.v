(** * Canonical mode-system instances

    Concrete [ModeSystem]s for the standard substructural disciplines (linear,
    affine, relevant, unrestricted) and the dual-mode systems DILL and
    judgmental S4, each in its own module so the names don't clash and can be
    imported individually. *)

Set Implicit Arguments.

From Stdlib.Classes Require Import RelationClasses.
From Sumatra.Autosubst Require Import fintype.
From Sumatra.Mode Require Import Core.
From Sumatra.Multiplicity Require Import Multiplicity MultiplicityInstances.

Local Open Scope sumatra_scope.

(* ================================================================= *)
(* Linear mode                                                       *)
(* ================================================================= *)

Module Lin.

  (** The single linear mode. *)
  Variant Mode : Type := Lin.

  #[export] Instance PreOrder_lin : PreOrder (fun _ _ : Mode => True).
  Proof. constructor; auto. Defined.

  #[export] Instance ModeSystem_lin : ModeSystem Mode := {|
    mode_sat  := fun _ _ => False;
    mode_mono := fun _ _ _ _ H => H;
  |}.

  (** [Lin] is a linear mode. *)
  Property Lin_lin : mode_lin Lin.
  Proof. split; auto. Qed.

End Lin.

(* ================================================================= *)
(* Affine mode                                                       *)
(* ================================================================= *)

Module Aff.

  (** The single affine mode. *)
  Variant Mode : Type := Aff.

  #[export] Instance PreOrder_aff : PreOrder (fun _ _ : Mode => True).
  Proof. constructor; auto. Defined.

  (** Affine: weakening is granted, contraction is not. *)
  #[export] Program Instance ModeSystem_aff : ModeSystem Mode := {|
    mode_sat  := fun P _ => match P with W => True | C => False end;
    mode_geq  := fun _ _ => True;
  |}.

  (** [Aff] is an affine mode. *)
  Property Aff_aff : mode_aff Aff.
  Proof. split; simpl; auto. Qed.

End Aff.

(* ================================================================= *)
(* Relevant (strict) mode                                            *)
(* ================================================================= *)

Module Rel.

  (** The single relevant (strict) mode. *)
  Variant Mode : Type := Rel.

  #[export] Instance PreOrder_rel : PreOrder (fun _ _ : Mode => True).
  Proof. constructor; auto. Defined.

  (** Relevant: contraction is granted, weakening is not. *)
  #[export] Program Instance ModeSystem_rel : ModeSystem Mode := {|
    mode_sat := fun P _ => match P with W => False | C => True end;
    mode_geq := fun _ _ => True;
  |}.

  (** [Rel] is a relevant mode. *)
  Property Rel_rel : mode_rel Rel.
  Proof. split; simpl; auto. Qed.

End Rel.

(* ================================================================= *)
(* Unrestricted (intuitionistic, structural) mode                    *)
(* ================================================================= *)

Module Unr.

  (** The single unrestricted (structural) mode. *)
  Variant Mode : Type := Unr.

  #[export] Instance PreOrder_unr : PreOrder (fun _ _ : Mode => True).
  Proof. constructor; auto. Defined.

  (** Unrestricted: every mode grants both weakening and contraction. *)
  #[export] Instance ModeSystem_unr : ModeSystem Mode := {|
    mode_sat  := fun _ _ => True;
    mode_geq  := fun _ _ => True;
    mode_mono := fun _ _ _ _ _ => I;
  |}.

  (** [Unr] is an unrestricted mode. *)
  Property Unr_unr : mode_unr Unr.
  Proof. split; exact I. Qed.

End Unr.

(* ================================================================= *)
(* Generic two-mode structure with [Hi ≥ Lo]                         *)
(* ================================================================= *)

(** A [DualModeSystem] is a two-mode structure with a low mode [Lo] below a high
    mode [Hi]. This yields the strictly-structural instances linear < affine,
    linear < relevant, linear < unrestricted (= DILL), affine < unrestricted,
    relevant < unrestricted, plus the four equal-discipline instances.

    The strictness assumption [ngeq_lo_hi] rules out identical lower and
    upper modes, even when they admit the same structural rules. *)

Class DualModeSystem (M : Type) := {
  dual_mode_system :: ModeSystem M;
  Lo : M;
  Hi : M;

  (** The two modes are distinct. *)
  distinct : Lo <> Hi;
  (** Every mode is decidably either [Lo] or [Hi]. *)
  mode_dec : forall m : M, {m = Lo} + {m = Hi};

  (** The preorder induced by the two-mode structure. *)
  geq_hi_lo  :   mode_geq Hi Lo;
  ngeq_lo_hi : ~ mode_geq Lo Hi;
}.

Section DualMode.
  Context {M : Type} `{BS : DualModeSystem M}.

  (** For any [R], [Lo ⊨ R] implies [Hi ⊨ R]. *)
  Property sat_mono :
    forall R : Struct,
      mode_sat R Lo ->
      mode_sat R Hi.
  Proof.
    intros P HLo. eapply mode_mono.
    - apply geq_hi_lo.
    - exact HLo.
  Qed.

  (** Propositional form of [mode_dec]. *)
  Definition mode_cases m :
    m = Lo \/ m = Hi :=
    match mode_dec m with
    | left H  => or_introl H
    | right H => or_intror H
    end.

End DualMode.

(* ================================================================= *)
(* DILL (dual intuitionistic linear logic)                           *)
(* ================================================================= *)

Module DILL.

  (** Two modes: linear [L] below unrestricted [U]. *)
  Variant Mode : Type := L | U.

  (** The preorder: U is strictly above L. *)
  Definition mode_geq_dill (m k : Mode) : Prop :=
    match m, k with
    | U, _ => True
    | L, L => True
    | L, U => False
    end.

  #[export] Instance PreOrder_dill : PreOrder mode_geq_dill.
  Proof.
    constructor.
    - intros [|]; exact I.
    - intros [|] [|] [|] H1 H2; simpl in *; tauto.
  Defined.

  (** The same system stated directly as a [ModeSystem]. *)
  #[export] Program Instance ModeSystem_dill : ModeSystem Mode := {|
    mode_sat := fun _ m => match m with U => True | L => False end;
    mode_geq := mode_geq_dill;
    mode_mono := ltac:(destruct m, k; auto);
  |}.

  (** DILL as a [DualModeSystem]: [U] is structural, [L] is linear. *)
  #[export] Instance DualModeSystem_dill : DualModeSystem Mode.
  Proof.
    refine {| Lo := L; Hi := U |}.
    - discriminate.
    - intros [|]; [left | right]; reflexivity.
    - constructor.
    - auto.
  Defined.

  (** [L] is a linear mode. *)
  Property L_lin : mode_lin L.
  Proof. split; auto. Qed.

  (** [U] is an unrestricted mode. *)
  Property U_unr : mode_unr U.
  Proof. split; exact I. Qed.

End DILL.

(* ================================================================= *)
(* S4 (Pfenning–Davies)                                              *)
(* ================================================================= *)

Module S4.

  (** Two unrestricted modes: valid [V] above true [U]. *)
  Variant Mode : Type := U | V.

  (** The preorder: [V] is strictly above [U]. *)
  Definition mode_geq_s4 (m k : Mode) : Prop :=
    match m, k with
    | V, _ => True
    | U, U => True
    | U, V => False
    end.

  #[export] Instance PreOrder_s4 : PreOrder mode_geq_s4.
  Proof.
    constructor.
    - intros [|]; exact I.
    - intros [|] [|] [|] H1 H2; simpl in *; tauto.
  Defined.

  (** The same system stated directly as a [ModeSystem]. *)
  #[export] Program Instance ModeSystem_s4 : ModeSystem Mode := {|
    mode_sat := fun _ _ => True;
    mode_geq := mode_geq_s4;
  |}.

  (** S4 as a [DualModeSystem]: both modes are structural, [V] above [U]. *)
  #[export] Instance DualModeSystem_s4 : DualModeSystem Mode.
  Proof.
    refine {| Lo := U; Hi := V |}.
    - discriminate.
    - intros [|]; [left | right]; reflexivity.
    - constructor.
    - auto.
  Defined.

  (** [U] (true) is an unrestricted mode. *)
  Property U_unr : mode_unr U.
  Proof. split; exact I. Qed.

  (** [V] (valid) is an unrestricted mode. *)
  Property V_unr : mode_unr V.
  Proof. split; exact I. Qed.

End S4.

(* ================================================================= *)
(* A joint linear/affine mode structure                              *)
(* ================================================================= *)

Module LinAff.

  (** Two modes: linear [Lin] below affine [Aff]. *)
  Variant Mode : Type := Lin | Aff.

  (** The preorder: [Aff] is strictly above [Lin]. *)
  Definition mode_geq_linaff (m k : Mode) : Prop :=
    match m, k with
    | Aff, _   => True
    | Lin, Lin => True
    | Lin, Aff => False
    end.

  #[export] Instance PreOrder_linaff : PreOrder mode_geq_linaff.
  Proof.
    constructor.
    - intros [|]; exact I.
    - intros [|] [|] [|] H1 H2; tauto.
  Defined.

  (** [Aff] satisfies [W] and nothing else; [Lin] satisfies nothing. *)
  #[export] Instance ModeSystem_linaff : ModeSystem Mode.
  Proof.
    refine {|
      mode_sat := fun P m =>
        match m, P with
        | Aff, W => True
        | _  , _ => False
        end;
      mode_geq := mode_geq_linaff
    |}.
    intros [|] [|] [|] Hgeq Hsat; tauto.
  Defined.

  (** The same system as a [DualModeSystem]. *)
  #[export] Instance DualModeSystem_linaff : DualModeSystem Mode.
  Proof.
    refine {| Lo := Lin; Hi := Aff |}.
    - discriminate.
    - intros [|]; [left | right]; reflexivity.
    - exact I.
    - simpl; tauto.
  Defined.

  (** [Lin] is a linear mode. *)
  Property Lin_lin : mode_lin Lin.
  Proof. split; auto. Qed.

  (** [Aff] is an affine mode. *)
  Property Aff_aff : mode_aff Aff.
  Proof. split; simpl; auto. Qed.

  (** Neither mode admits contraction. *)
  Property no_contraction (m : Mode) : ~ m ⊨ C.
  Proof. destruct m; tauto. Qed.

End LinAff.

(* ================================================================= *)
(* The substructural lattice: all four disciplines, mixed             *)
(* ================================================================= *)

Module Sub.

  (** [Sub] packages all four canonical substructural disciplines into one
      [ModeSystem], ordered as [Unr ≥ Aff ≥ Lin] and [Unr ≥ Rel ≥ Lin] (with
      [Aff] and [Rel] incomparable). *)
  Variant Mode : Type := Lin | Aff | Rel | Unr.

  (** Whether a mode grants weakening / contraction, as a boolean. *)
  Definition has_w (m : Mode) : bool :=
    match m with Aff | Unr => true | Lin | Rel => false end.
  Definition has_c (m : Mode) : bool :=
    match m with Rel | Unr => true | Lin | Aff => false end.

  Definition sub_geq (m k : Mode) : Prop :=
    (has_w k = true -> has_w m = true) /\ (has_c k = true -> has_c m = true).

  #[export] Instance PreOrder_sub : PreOrder sub_geq.
  Proof.
    constructor.
    - intro m; split; auto.
    - intros m k l [Hw1 Hc1] [Hw2 Hc2]; split; auto.
  Defined.

  #[export, refine] Instance ModeSystem_sub : ModeSystem Mode := {|
    mode_sat := fun P m => match P with
                            | W => has_w m = true
                            | C => has_c m = true
                            end;
    mode_geq := sub_geq;
  |}.
  Proof. intros m k [] Hgeq Hk; [apply Hgeq | apply Hgeq]; exact Hk. Defined.

  (** Each mode classifies as expected. *)
  Property Lin_lin : mode_lin Lin.
  Proof. split; intro H; discriminate H. Qed.
  Property Aff_aff : mode_aff Aff.
  Proof. split; [reflexivity | intro H; discriminate H]. Qed.
  Property Rel_rel : mode_rel Rel.
  Proof. split; [intro H; discriminate H | reflexivity]. Qed.
  Property Unr_unr : mode_unr Unr. Proof. split; reflexivity. Qed.

  (** The diamond order: [Lin] is the bottom, [Unr] the top, and
      [Aff]/[Rel] are incomparable. *)
  Property Lin_bottom (m : Mode) : m ≥ Lin.
  Proof. split; discriminate. Qed.
  Property Unr_top (m : Mode) : Unr ≥ m.
  Proof. split; intro; reflexivity. Qed.
  Property Aff_nge_Rel : ~ Aff ≥ Rel.
  Proof. intros [_ Hc]; discriminate (Hc eq_refl). Qed.
  Property Rel_nge_Aff : ~ Rel ≥ Aff.
  Proof. intros [Hw _]; discriminate (Hw eq_refl). Qed.

End Sub.
