From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

From Autosubst Require Import Autosubst.

From Coq Require Import List.
Import ListNotations.

(* ---------------- *)
(* termos canónicos *)

Inductive term: Type :=
| Vari (x: var)
| Lamb (t: {bind term})
| VariApp (x: var) (u: term) (l: list term)
| LambApp (t: {bind term}) (u: term) (l: list term).

Section dedicated_induction_principle.
  Variable P : term -> Prop.
  Variable Q : list term -> Prop.

  Hypothesis HVari : forall x, P (Vari x).
  Hypothesis HLamb : forall t, P t -> P (Lamb t).
  Hypothesis HVariApp : forall x u l, P u -> Q l -> P (VariApp x u l).
  Hypothesis HLambApp : forall t u l, P t -> P u -> Q l -> P (LambApp t u l).
  Hypothesis HNil : Q [].
  Hypothesis HCons : forall u l, P u -> Q l -> Q (u::l).

  Proposition sim_term_ind : forall t, P t.
  Proof.
    fix rec 1. destruct t.
    - now apply HVari.
    - apply HLamb. now apply rec.
    - apply HVariApp.
      + now apply rec.
      + assert (forall l, Q l). {
            fix rec' 1. destruct l0.
            - apply HNil.
            - apply HCons.
              + now apply rec.
              + now apply rec'. }          
        now apply H.
    - apply HLambApp.
      + now apply rec.
      + now apply rec.
      + assert (forall l, Q l). {
            fix rec' 1. destruct l0.
            - apply HNil.
            - apply HCons.
              + now apply rec.
              + now apply rec'. }          
        now apply H.
  Qed.      

  Proposition sim_list_ind : (forall l, Q l).
  Proof.
    fix rec 1. destruct l.
    - now apply HNil.
    - apply HCons.
      + now apply sim_term_ind.
      + now apply rec.
  Qed.          
End dedicated_induction_principle.

Combined Scheme mut_term_ind from sim_term_ind, sim_list_ind.

(* app brings a value to the head of an application *)
(* ------------------------------------------------ *) 

Definition app (t u: term) (l: list term): term :=
  match t with
  | Vari x => VariApp x u l
  | Lamb t' => LambApp t' u l
  | VariApp x u' l' => VariApp x u' (l' ++ u::l)
  | LambApp t' u' l' => LambApp t' u' (l' ++ u::l)
  end.

Notation "t '@(' u ',' l ')'" := (app t u l) (at level 9).

(* substituição *)
(* ------------ *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. 
Proof.
  unfold Subst. fix inst 2. change _ with (Subst term) in inst.
  intros σ s. change (annot term s). destruct s.
  - exact (σ x).
  - exact (Lamb (subst (up σ) t)).
  - exact ((σ x)@(subst σ s, mmap (subst σ) l)).
  - exact (LambApp (subst (up σ) t) (subst σ s) (mmap (subst σ) l)).
Defined.

Lemma rename_subst :
  (forall s xi, rename xi s = s.[ren xi])
  /\
  (forall (l: list term) xi, mmap (rename xi) l = l..[ren xi]).
Proof.
  apply mut_term_ind ; intros ; simpl ; f_equal ;
    try rewrite up_upren_internal ; asimpl ; auto.
  - apply H0.
Qed.

Lemma subst_id :
  (forall s, s.[ids] = id s)
  /\
  (forall (l: list term), l..[ids] = id l).
Proof.
  apply mut_term_ind ; intros ; simpl in * ; f_equal ;
    try rewrite up_id_internal ; auto.
Qed.

Lemma ren_subst_comp :
  (forall s xi sigma, (rename xi s).[sigma] = s.[xi >>> sigma])
  /\
  (forall (l: list term) xi sigma, (mmap (rename xi) l)..[sigma] = l..[xi >>> sigma]).
Proof.
  apply mut_term_ind ; intros ; simpl ; f_equal ;
    try rewrite up_comp_ren_subst ; msimpl ; auto.
  - apply H0.
Qed.

Lemma mmap_append (A: Type) (l1 l2: list A) (f: A -> A) :
  mmap f (l1 ++ l2) = (mmap f l1) ++ (mmap f l2).
Proof.
  induction l1 ; asimpl ; try rewrite IHl1 ; auto.
Qed.

Hint Resolve mmap_append : core.
  
Lemma app_subst_comm t u l σ:
  (t@(u,l)).[σ] = t.[σ]@(u.[σ], l..[σ]).
Proof.
  destruct t ; intros ; asimpl ; try easy.
  - destruct (σ x) ; asimpl ; f_equal ; auto.
    + rewrite<- app_assoc. f_equal.
      rewrite<- app_comm_cons. f_equal.
      now apply mmap_append.
    + rewrite<- app_assoc. f_equal.
      rewrite<- app_comm_cons. f_equal.
      now apply mmap_append.
  - now rewrite mmap_append.
Qed.
      
Lemma subst_ren_comp :
  (forall s xi sigma, rename xi s.[sigma] = s.[sigma >>> rename xi])
  /\
  (forall (l: list term) xi sigma, mmap (rename xi) l..[sigma] = l..[sigma >>> rename xi]).
Proof.
  apply mut_term_ind ; intros ; asimpl ; auto.
  - f_equal. rewrite up_comp_subst_ren_internal ; auto.
    + intros. apply rename_subst.
    + intros. apply ren_subst_comp.
  - rewrite (proj1 rename_subst). rewrite app_subst_comm. f_equal.
    + symmetry. apply rename_subst.
    + rewrite<- (proj1 rename_subst). apply H.
    + rewrite<- H0. msimpl. repeat f_equal.
      f_ext. intro. now rewrite (proj1 rename_subst).
  - f_equal.
    + rewrite up_comp_subst_ren_internal ; auto.
      * intros. apply rename_subst.
      * intros. apply ren_subst_comp.
    + apply H0.
    + rewrite<- H1. now msimpl.
  - f_equal.
    + now apply H.
    + rewrite<- H0. now msimpl.
Qed.

Lemma subst_comp :
  (forall s sigma tau, s.[sigma].[tau] = s.[sigma >> tau])
  /\
  (forall (l: list term) sigma tau, l..[sigma]..[tau] = l..[sigma >> tau]).
Proof.
  apply mut_term_ind ; intros ; asimpl ; f_equal ; auto.
  - rewrite up_comp_internal ; auto.
    + intros. apply ren_subst_comp.
    + intros. apply subst_ren_comp.
  - rewrite app_subst_comm ; f_equal ; auto.
  - rewrite up_comp_internal ; auto.
    + intros. apply ren_subst_comp.
    + intros. apply subst_ren_comp.
  - rewrite<- H1. now msimpl.
  - rewrite<- H0. now msimpl.    
Qed.
    
Instance SubstLemmas_term : SubstLemmas term.
Proof.
  constructor.
  - intros. apply rename_subst.
  - apply subst_id.
  - reflexivity.
  - intros. apply subst_comp.
Qed.
    
Section Compatibilty.

  Variable base : relation term.
  
  Inductive comp : relation term :=
  | Comp_Lamb (t t': {bind term}) :
    comp t t' -> comp (Lamb t) (Lamb t')
  | Comp_VariApp1 x u u' l :
    comp u u' -> comp (VariApp x u l) (VariApp x u' l)
  | Comp_VariApp2 x u l l' :
    comp' l l' -> comp (VariApp x u l) (VariApp x u l')
  | Comp_LambApp1 (t t': {bind term}) u l :
    comp t t' -> comp (LambApp t u l) (LambApp t' u l)
  | Comp_LambApp2 (t: {bind term}) u u' l :
    comp u u' -> comp (LambApp t u l) (LambApp t u' l)
  | Comp_LambApp3 (t: {bind term}) u l l' :
    comp' l l' -> comp (LambApp t u l) (LambApp t u l')
  | Step_Base t t' : base t t' -> comp t t'

  with comp' : relation (list term) :=
  | Comp_Head u u' l : comp u u' -> comp' (u::l) (u'::l)
  | Comp_Tail u l l' : comp' l l' -> comp' (u::l) (u::l').

  Scheme sim_comp_ind := Induction for comp Sort Prop
    with sim_comp_ind' := Induction for comp' Sort Prop.

End Compatibilty.

Combined Scheme mut_comp_ind from sim_comp_ind, sim_comp_ind'.

Hint Constructors comp comp' : core.

Section IsCompatible.

  Variable R : relation term.
  Variable R' : relation (list term).

  Record is_compatible := {
    comp_lamb : forall t t': {bind term}, R t t' -> R (Lamb t) (Lamb t') ;
    comp_variApp1 : forall x u u' l, R u u' -> R (VariApp x u l) (VariApp x u' l) ;
    comp_variApp2 : forall x u l l', R' l l' -> R (VariApp x u l) (VariApp x u l') ;
    comp_lambApp1 : forall (t t': {bind term}) u l, R t t' -> R (LambApp t u l) (LambApp t' u l) ;
    comp_lambApp2 : forall (t: {bind term}) u u' l, R u u' -> R (LambApp t u l) (LambApp t u' l) ;
    comp_lambApp3 : forall (t: {bind term}) u l l', R' l l' -> R (LambApp t u l) (LambApp t u l') ;
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

Inductive β1: relation term :=
| Step_Beta1 (t: {bind term}) (t' u: term) :
  t' = t.[u .: ids] -> β1 (LambApp t u []) t'.

Inductive β2: relation term :=
| Step_Beta2 (t: {bind term}) (t' u v: term) l :
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
    intros l1 l1' H.
    induction H ; intros.
    - repeat rewrite<- app_comm_cons.
      now constructor. 
    - repeat rewrite<- app_comm_cons.
      constructor. now apply IHcomp'.
  Qed.    

  Lemma step_comp_append2 :
    forall l2 l2', step' l2 l2' -> forall l1, step' (l1 ++ l2) (l1 ++ l2').
  Proof.
    intros. induction l1 ; asimpl ; auto.
  Qed.    
  
  Lemma step_comp_app1 :
    forall v v', step v v' -> forall u l, step v@(u,l) v'@(u,l).
  Proof.
    intros v v' H.
    destruct H ; intros ; asimpl ;
      constructor ; try apply step_comp_append1 ; try easy.
    - inversion H.
      + inversion H0 ; subst ; asimpl.
        right. now constructor. 
      + inversion H0 ; subst ; asimpl.
        right. constructor.
        destruct (t0.[u0/]) ; asimpl ;
          f_equal ; now rewrite<- app_assoc. 
  Qed.

  Proposition multistep_comp_app1 :
    forall v v' u l, multistep v v' -> multistep v@(u,l) v'@(u,l).
  Proof.
    intros. induction H.
    - constructor.
    - apply rt1n_trans with (y@(u,l)) ; try easy.
      + now apply step_comp_app1. 
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
    - apply rt1n_trans with (v@(y,l)) ; try easy.
      + now apply step_comp_app2. 
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
    - apply rt1n_trans with (v@(u,y)) ; try easy.
      + now apply step_comp_app3. 
  Qed.
  
End CompatibilityLemmas.

(* Canonical terms in β normal form *) 
(* -------------------------------- *) 

Inductive normal: term -> Prop :=
| nVari x : normal (Vari x)
| nLamb t : normal t -> normal (Lamb t)
| nApp x u l : normal u -> normal_list l -> normal (VariApp x u l)
  
with normal_list: list term -> Prop :=
| nNil : normal_list []
| nCons u l : normal u -> normal_list l -> normal_list (u::l).

Scheme sim_normal_ind := Induction for normal Sort Prop
  with sim_normal_list_ind := Induction for normal_list Sort Prop.  

Combined Scheme mut_normal_ind from sim_normal_ind, sim_normal_list_ind.

(* Typing Rules *)
(* ------------ *)

Require Import SimpleTypes.

Inductive sequent (Γ: var->type) : term -> type -> Prop := 
| varAxiom (x: var) (A: type) :
  Γ x = A -> sequent Γ (Vari x) A

| Right (t: term) (A B: type) :
  sequent (A .: Γ) t B -> sequent Γ (Lamb t) (Arr A B)
                                 
| Left (x: var) (u: term) (l: list term) (A B C: type) :
  Γ x = (Arr A B) -> sequent Γ u A -> list_sequent Γ B l C ->
  sequent Γ (VariApp x u l) C

| KeyCut (t: {bind term}) (u: term) (l: list term) (A B C: type) :
  sequent (A .: Γ) t B -> sequent Γ u A -> list_sequent Γ B l C ->
  sequent Γ (LambApp t u l) C

with list_sequent (Γ:var->type) : type -> (list term) -> type -> Prop :=
| nilAxiom (C: type) : list_sequent Γ C [] C

| Lft (u: term) (l: list term) (A B C:type) :
  sequent Γ u A -> list_sequent Γ B l C ->
  list_sequent Γ (Arr A B) (u :: l) C.

Hint Constructors sequent list_sequent : core.

Scheme sim_sequent_ind := Induction for sequent Sort Prop
  with sim_list_sequent_ind := Induction for list_sequent Sort Prop.

Combined Scheme mut_sequent_ind from sim_sequent_ind, sim_list_sequent_ind.
