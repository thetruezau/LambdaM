Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* ---------------- *)
(* termos canónicos *)

Inductive λc: Type :=
| Vari (x: var)
| Lamb (t: {bind λc})
| VariApp (x: var) (u: λc) (l: list λc)
| LambApp (t: {bind λc}) (u: λc) (l: list λc).

Section simultaneous_induction_principle.
  Variable P : λc -> Prop.

  Hypothesis HVari : forall x, P (Vari x).
  Hypothesis HLamb : forall t, P t -> P (Lamb t).
  Hypothesis HVariApp : forall x u l, P u -> Forall P l ->
                              P (VariApp x u l).
  Hypothesis HLambApp : forall t u l, P t -> P u -> Forall P l ->
                                 P (LambApp t u l).

  Proposition sim_λc_ind : forall t, P t.
  Proof.
    fix rec 1. destruct t.
    - apply HVari.
    - apply HLamb. apply rec.
    - apply HVariApp.
      + apply rec.
      + assert (forall l, Forall P l). fix rec' 1. destruct l0.
        * apply Forall_nil.
        * apply Forall_cons ; [ apply rec | apply rec' ].
        * apply H.
    - apply HLambApp.
      + apply rec.
      + apply rec.
      + assert (forall l, Forall P l). fix rec' 1. destruct l0.
        * apply Forall_nil.
        * apply Forall_cons ; [ apply rec | apply rec' ].
        * apply H.
  Qed.
End simultaneous_induction_principle.

Definition app (t u: λc) (l: list λc): λc :=
  match t with
  | Vari x => VariApp x u l
  | Lamb t' => LambApp t' u l
  | VariApp x u' l' => VariApp x u' (l' ++ u::l)
  | LambApp t' u' l' => LambApp t' u' (l' ++ u::l)
  end.

Notation "t '@(' u ',' l ')'" := (app t u l) (at level 9).

(* substituição *)
(* ------------ *)

Instance Ids_λc : Ids λc. derive. Defined.
Instance Rename_λc : Rename λc. derive. Defined.
Instance Subst_λc : Subst λc. 
Proof.
  unfold Subst. fix inst 2. change _ with (Subst λc) in inst.
  intros σ s. change (annot λc s). destruct s.
  - exact (σ x).
  - exact (Lamb (subst (up σ) t)).
  - exact ((σ x)@(subst σ s, mmap (subst σ) l)).
  - exact (LambApp (subst (up σ) t) (subst σ s) (mmap (subst σ) l)).
Defined.

Lemma rename_subst : forall s xi, rename xi s = s.[ren xi].
Proof.
  induction s using sim_λc_ind ; intros ; simpl ; f_equal ;
    try rewrite up_upren_internal ; auto.
  - induction H ; asimpl ; f_equal ; auto.
  - induction H ; asimpl ; f_equal ; auto.
Qed.

Lemma subst_id : forall s, s.[ids] = id s.
Proof.
  induction s using sim_λc_ind ; intros ; simpl ; f_equal ;
    try rewrite up_id_internal ; auto.
  - induction H ; asimpl ; f_equal ; auto.
  - induction H ; asimpl ; f_equal ; auto.
Qed.

Lemma ren_subst_comp :
  forall s xi sigma, (rename xi s).[sigma] = s.[xi >>> sigma].
Proof.
  induction s using sim_λc_ind ; intros ; simpl ; f_equal ;
    try rewrite up_comp_ren_subst ; auto.
  - induction H ; msimpl ; f_equal ; auto.
  - induction H ; msimpl ; f_equal ; auto.
Qed.

Lemma mmap_append (A: Type) (l1 l2: list A) (f: A -> A) :
  mmap f (l1 ++ l2) = (mmap f l1) ++ (mmap f l2).
Proof.
  induction l1 ; asimpl ; try rewrite IHl1 ; auto.
Qed.

Hint Resolve mmap_append : core.
  
Lemma app_subst_comm : forall t u l σ, (t@(u,l)).[σ] = t.[σ]@(u.[σ], l..[σ]).
Proof.
  induction t using sim_λc_ind ; intros ; asimpl.
  - reflexivity.
  - f_equal.
  - destruct (σ x) ; asimpl ; f_equal.
    + apply mmap_append.
    + apply mmap_append.
    + rewrite<- app_assoc. f_equal.
      rewrite<- app_comm_cons. f_equal.
      apply mmap_append.
    + rewrite<- app_assoc. f_equal.
      rewrite<- app_comm_cons. f_equal.
      apply mmap_append.
  - f_equal. apply mmap_append.
Qed.
      
Lemma subst_ren_comp :
  forall s xi sigma, rename xi s.[sigma] = s.[sigma >>> rename xi].
Proof.
  induction s using sim_λc_ind ; intros ; asimpl ; f_equal ; auto.
  - rewrite up_comp_subst_ren_internal ; auto.
    + intros. apply rename_subst.
    + intros. apply ren_subst_comp.
  - rewrite rename_subst. rewrite app_subst_comm. f_equal.
    + symmetry. apply rename_subst.
    + rewrite<- rename_subst. apply IHs.
    + induction H ; asimpl ; f_equal.
      * rewrite<- rename_subst. apply H.
      * rewrite<- mmap_comp. apply IHForall.
  - rewrite up_comp_subst_ren_internal ; auto.
    + intros. apply rename_subst.
    + intros. apply ren_subst_comp.
  - induction H ; asimpl ; f_equal ; auto.
Qed.

Lemma subst_comp :
  forall s sigma tau, s.[sigma].[tau] = s.[sigma >> tau].
Proof.
  induction s using sim_λc_ind ; intros ; asimpl ; f_equal ; auto.
  - rewrite up_comp_internal ; auto.
    + intros. apply ren_subst_comp.
    + intros. apply subst_ren_comp.
  - rewrite app_subst_comm ; f_equal ; auto.
    + induction H ; msimpl ; f_equal ; auto.
  - rewrite up_comp_internal ; auto.
    + intros. apply ren_subst_comp.
    + intros. apply subst_ren_comp.
  - induction H ; msimpl ; f_equal ; auto.
Qed.
    
Instance SubstLemmas_λc : SubstLemmas λc.
Proof.
  constructor.
  - intros. apply rename_subst.
  - apply subst_id.
  - reflexivity.
  - intros. apply subst_comp.
Qed.
    
Section Compatibilty.

  Variable base : relation λc.
  
  Inductive comp : relation λc :=
  | Comp_Lamb (t t': {bind λc}) :
    comp t t' -> comp (Lamb t) (Lamb t')
  | Comp_VariApp1 x u u' l :
    comp u u' -> comp (VariApp x u l) (VariApp x u' l)
  | Comp_VariApp2 x u l l' :
    comp' l l' -> comp (VariApp x u l) (VariApp x u l')
  | Comp_LambApp1 (t t': {bind λc}) u l :
    comp t t' -> comp (LambApp t u l) (LambApp t' u l)
  | Comp_LambApp2 (t: {bind λc}) u u' l :
    comp u u' -> comp (LambApp t u l) (LambApp t u' l)
  | Comp_mApp3 (t: {bind λc}) u l l' :
    comp' l l' -> comp (LambApp t u l) (LambApp t u l')
  | Step_Base t t' : base t t' -> comp t t'

  with comp' : relation (list λc) :=
  | Comp_Head u u' l : comp u u' -> comp' (u::l) (u'::l)
  | Comp_Tail u l l' : comp' l l' -> comp' (u::l) (u::l').

  Scheme sim_comp_ind := Induction for comp Sort Prop
    with sim_comp_ind' := Induction for comp' Sort Prop.

End Compatibilty.

Hint Constructors comp comp' : core.

Section IsCompatible.

  Variable R : relation λc.
  Variable R' : relation (list λc).

  Record is_compatible := {
    comp_lamb : forall t t': {bind λc}, R t t' -> R (Lamb t) (Lamb t') ;
    comp_variApp1 : forall x u u' l, R u u' -> R (VariApp x u l) (VariApp x u' l) ;
    comp_variApp2 : forall x u l l', R' l l' -> R (VariApp x u l) (VariApp x u l') ;
    comp_lambApp1 : forall (t t': {bind λc}) u l, R t t' -> R (LambApp t u l) (LambApp t' u l) ;
    comp_lambApp2 : forall (t: {bind λc}) u u' l, R u u' -> R (LambApp t u l) (LambApp t u' l) ;
    comp_lambApp3 : forall (t: {bind λc}) u l l', R' l l' -> R (LambApp t u l) (LambApp t u l') ;
    comp_head : forall u u' l, R u u' -> R' (u::l) (u'::l) ;
    comp_tail : forall u l l', R' l l' -> R' (u::l) (u::l')
    }.
  
End IsCompatible.

Theorem clos_refl_trans_pres_comp :
  forall R R', is_compatible R R' ->
          is_compatible (clos_refl_trans_1n _ R) (clos_refl_trans_1n _ R').
Proof.
  intros. destruct H. 
  split ; intros ; induction H ; econstructor ; eauto. 
Qed.  

(* Redução em λm *)
(* ------------- *)

Inductive β1: relation λc :=
| Step_Beta1 (t: {bind λc}) (t' u: λc) :
  t' = t.[u .: ids] -> β1 (LambApp t u []) t'.

Inductive β2: relation λc :=
| Step_Beta2 (t: {bind λc}) (t' u v: λc) l :
  t' = t.[u .: ids]@(v,l) -> β2 (LambApp t u (v::l)) t'.

Definition step := comp (union _ β1 β2).
Definition step' := comp' (union _ β1 β2).

Hint Unfold step step' : core.

Proposition step_is_compatible : is_compatible step step'.
Proof.
  split ; autounfold ; intros ; constructor ; assumption.
Qed.

Definition multistep := clos_refl_trans_1n _ step.
Definition multistep' := clos_refl_trans_1n _ step'.

Proposition multistep_is_compatible :
  is_compatible multistep multistep'.
Proof.
  apply clos_refl_trans_pres_comp. apply step_is_compatible.
Qed.  

Section CompatibilityLemmas.

  Lemma step_comp_append1 :
    forall l1 l1', step' l1 l1' -> forall l2, step' (l1 ++ l2) (l1' ++ l2).
  Proof.
    intros l1 l1' H. induction H ; intros.
    - repeat rewrite<- app_comm_cons.
      constructor. assumption.
    - repeat rewrite<- app_comm_cons.
      constructor. apply IHcomp'.
  Qed.    

  Lemma step_comp_append2 :
    forall l2 l2', step' l2 l2' -> forall l1, step' (l1 ++ l2) (l1 ++ l2').
  Proof.
    intros. induction l1 ; asimpl ; auto.
  Qed.    
  
  Lemma step_comp_app1 :
    forall v v', step v v' -> forall u l, step v@(u,l) v'@(u,l).
  Proof.
    intros v v' H. induction H ; intros ; asimpl ;
      constructor ; try apply step_comp_append1 ; try assumption.
    - inversion H.
      + inversion H0 ; subst ; asimpl.
        right. constructor. reflexivity.
      + inversion H0 ; subst ; asimpl.
        right. constructor.
        destruct (t0.[u0/]) ; asimpl ; f_equal.
      * rewrite<- app_assoc. reflexivity.
      * rewrite<- app_assoc. reflexivity.
  Qed.

  Proposition multistep_comp_app1 :
    forall v v' u l, multistep v v' -> multistep v@(u,l) v'@(u,l).
  Proof.
    intros. induction H.
    - constructor.
    - apply rt1n_trans with (y@(u,l)).
      + apply step_comp_app1. assumption.
      + assumption.
  Qed.
  
  Lemma step_comp_app2 :
    forall v u u' l, step u u' -> step v@(u,l) v@(u',l).
  Proof.
    pose step_is_compatible.
    
    intros. destruct v ; asimpl.
    - apply comp_variApp1 with step' ; auto.
    - apply comp_lambApp2 with step' ; auto.
    - apply comp_variApp2 with step' ; auto.
      + apply step_comp_append2. auto.
    - apply comp_lambApp3 with step' ; auto.
      + apply step_comp_append2. auto.
  Qed.

  Proposition multistep_comp_app2 :
    forall v u u' l, multistep u u' -> multistep v@(u,l) v@(u',l).
  Proof.
    intros. induction H.
    - constructor.
    - apply rt1n_trans with (v@(y,l)).
      + apply step_comp_app2. assumption.
      + assumption.
  Qed.
  
  Lemma step_comp_app3 :
    forall v u l l', step' l l' -> step v@(u,l) v@(u,l').
  Proof.
    pose step_is_compatible.
    
    intros. destruct v ; asimpl.
    - apply comp_variApp2 with step' ; auto.
    - apply comp_lambApp3 with step' ; auto.
    - apply comp_variApp2 with step' ; auto.
      + apply step_comp_append2. auto.
    - apply comp_lambApp3 with step' ; auto.
      + apply step_comp_append2. auto.
  Qed.
  
  Proposition multistep_comp_app3 :
    forall v u l l', multistep' l l' -> multistep v@(u,l) v@(u,l').
  Proof.
    intros. induction H.
    - constructor.
    - apply rt1n_trans with (v@(u,y)).
      + apply step_comp_app3. assumption.
      + assumption.
  Qed.
  
End CompatibilityLemmas.

Section StepSubstitution.

  Lemma step_subst :
    forall s t, step s t -> forall σ, step s.[σ] t.[σ].
  Proof.
    intros s t H.
    induction H using sim_comp_ind
      with (P0 := fun l l' (_: step' l l') =>
                    forall σ, step' l..[σ] l'..[σ]) ;
      intros ; autounfold ; asimpl ;
      try (now constructor ; apply IHcomp).
    - destruct (σ x) ; asimpl ; constructor.
      + apply IHcomp.
      + apply IHcomp.
      + induction l0 ; asimpl ; constructor.
        * apply IHcomp.
        * apply IHl0.
      + induction l0 ; asimpl ; constructor.
        * apply IHcomp.
        * apply IHl0.
    - destruct (σ x) ; asimpl ; constructor.
      + apply IHcomp.
      + apply IHcomp.
      + induction l0 ; asimpl ; constructor.
        * apply IHcomp.
        * apply IHl0.
      + induction l0 ; asimpl ; constructor.
        * apply IHcomp.
        * apply IHl0.
    - destruct b as [Beta1 | Beta2] ; constructor.
      + induction Beta1. subst. left. constructor. autosubst.
      + induction Beta2. subst. right. asimpl. constructor.
        rewrite app_subst_comm. f_equal. autosubst.
  Qed.

End StepSubstitution.
