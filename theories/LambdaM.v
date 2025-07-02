From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

From Autosubst Require Import Autosubst.

From Coq Require Import List.
Import ListNotations.

(* Sintaxe *)
(* ------- *)

Inductive term: Type :=
| Var (x: var)
| Lam (t: {bind term})
| mApp (t: term) (u: term) (l: list term).

Section dedicated_induction_principle.
  Variable P : term -> Prop.
  Variable Q : list term -> Prop.
  
  Hypothesis HVar : forall x, P (Var x).
  Hypothesis HLam : forall t: {bind term}, P t -> P (Lam t).
  Hypothesis HmApp : forall t u l, P t -> P u -> Q l -> P (mApp t u l).
  Hypothesis HNil : Q [].
  Hypothesis HCons : forall u l, P u -> Q l -> Q (u::l).
  
  Proposition sim_term_ind : forall t, P t.
  Proof.
    fix rec 1. destruct t.
    - now apply HVar.
    - apply HLam. now apply rec.
    - apply HmApp.
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
  
  Proposition sim_list_ind : forall l, Q l.
  Proof.
    fix rec 1. destruct l.
    - now apply HNil.
    - apply HCons.
      + now apply sim_term_ind.
      + now apply rec.
  Qed.          
End dedicated_induction_principle.

Combined Scheme mut_term_ind from sim_term_ind, sim_list_ind.

(* Substituição *)
(* ------------ *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

(* Definição de compatibilidade em λm *)
(* ---------------------------------- *)

Section Compatibilty.

  Variable base : relation term.
  
  Inductive comp : relation term :=
  | Comp_Lam (t t': {bind term}) : comp t t' ->
                                   comp (Lam t) (Lam t')
  | Comp_mApp1 t t' u l : comp t t' ->
                          comp (mApp t u l) (mApp t' u l)
  | Comp_mApp2 t u u' l : comp u u' ->
                          comp (mApp t u l) (mApp t u' l)
  | Comp_mApp3 t u l l' : comp' l l' ->
                          comp (mApp t u l) (mApp t u l')
  | Step_Base t t' : base t t' -> comp t t'

  with comp' : relation (list term) :=
  | Comp_Head u u' l : comp u u' -> comp' (u::l) (u'::l)
  | Comp_Tail u l l' : comp' l l' -> comp' (u::l) (u::l').

  Scheme sim_comp_ind := Induction for comp Sort Prop
    with sim_comp_ind' := Induction for comp' Sort Prop.

  Combined Scheme mut_comp_ind from sim_comp_ind, sim_comp_ind'.
  
  Hint Constructors comp comp' : core.
End Compatibilty.

Section IsCompatible.

  Variable R : relation term.
  Variable R' : relation (list term).

  Record is_compatible := {
      comp_lam : forall t t': {bind term}, R t t' -> R (Lam t) (Lam t') ;
      comp_mApp1 : forall t t' u l, R t t' -> R (mApp t u l) (mApp t' u l) ;
      comp_mApp2 : forall t u u' l, R u u' -> R (mApp t u l) (mApp t u' l) ;
      comp_mApp3 : forall t u l l', R' l l' -> R (mApp t u l) (mApp t u l') ;
      comp_head : forall u u' l, R u u' -> R' (u :: l) (u' :: l) ;
      comp_tail : forall u l l', R' l l' -> R' (u :: l) (u :: l')
    }.
  
End IsCompatible.

Theorem comp_is_compatible B : is_compatible (comp B) (comp' B).
Proof.
  split ; autounfold ; intros ; constructor ; assumption.
Qed.

Theorem clos_refl_trans_pres_comp :
  forall R R', is_compatible R R' ->
          is_compatible (clos_refl_trans_1n _ R) (clos_refl_trans_1n _ R').
Proof.
  intros R R' H. destruct H. 
  (* esta tática resolve todos os goals! *)      
  split ; intros ; induction H ; econstructor ; eauto.
Qed.
  
(* Redução em λm *)
(* ------------- *)

Inductive β1: relation term :=
| Step_Beta1 (t: {bind term}) (t' u: term) :
  t' = t.[u .: ids] -> β1 (mApp (Lam t) u []) t'.

Inductive β2: relation term :=
| Step_Beta2 (t: {bind term}) (t' u v: term) l :
  t' = t.[u .: ids] -> β2 (mApp (Lam t) u (v::l)) (mApp t' v l).

Inductive H: relation term :=       
| Step_H (t u u': term) l l' l'' :
  l'' = l ++ (u'::l') -> H (mApp (mApp t u l) u' l') (mApp t u l'').

Definition step := comp (union _ (union _ β1 β2) H).
Definition step' := comp' (union _ (union _ β1 β2) H).
Hint Unfold step step' : core.

Definition step_β := comp (union _ β1 β2).
Definition step_β' := comp' (union _ β1 β2).
Hint Unfold step_β step_β' : core.

Definition step_H := comp H.
Definition step_H' := comp' H.
Hint Unfold step_H step_H' : core.

Definition multistep := clos_refl_trans_1n _ step.
Definition multistep' := clos_refl_trans_1n _ step'.
Hint Unfold multistep multistep': core.

Definition multistep_H := clos_refl_trans_1n _ step_H.
Definition multistep_H' := clos_refl_trans_1n _ step_H'.
Hint Unfold multistep_H multistep_H': core.

Corollary step_is_compatible : is_compatible step step'.
Proof. now apply comp_is_compatible. Qed.

Corollary multistep_is_compatible : is_compatible multistep multistep'.
Proof. apply clos_refl_trans_pres_comp. apply step_is_compatible. Qed.

Proposition step_H_is_compatible : is_compatible step_H step_H'.
Proof. apply comp_is_compatible. Qed.

Corollary multistep_H_is_compatible :
  is_compatible multistep_H multistep_H'.
Proof. apply clos_refl_trans_pres_comp. apply step_H_is_compatible. Qed.

Proposition step_H_inclusion :
  (forall t t', step_H t t' -> step t t')
  /\
  (forall l l', step_H' l l' -> step' l l').
Proof.
  (* instead of giving hints to auto tactic *)
  pose step_is_compatible as Hm. destruct Hm.
  
  apply mut_comp_ind ; intros ; auto.
  - inversion b ; subst.
    constructor. now right. 
Qed.        
  
Proposition multistep_H_inclusion t t' :
  multistep_H t t' -> multistep t t'.
Proof.
  intro .
  induction H0.
  - constructor.
  - apply rt1n_trans with y ; try easy.
    + now apply step_H_inclusion.
Qed.
  
(* Typing Rules *)
(* ------------ *)

Require Import SimpleTypes.

Inductive sequent (Γ: var->type) : term -> type -> Prop := 
| varAxiom (x: var) (A: type) :
  Γ x = A -> sequent Γ (Var x) A

| Right (t: term) (A B: type) :
  sequent (A .: Γ) t B -> sequent Γ (Lam t) (Arr A B)

| HeadCut (t u: term) (l: list term) (A B C: type) :
  sequent Γ t (Arr A B) -> sequent Γ u A -> list_sequent Γ B l C ->
  sequent Γ (mApp t u l) C

with list_sequent (Γ:var->type) : type -> (list term) -> type -> Prop :=
| nilAxiom (C: type) : list_sequent Γ C [] C

| Lft (u: term) (l: list term) (A B C:type) :
  sequent Γ u A -> list_sequent Γ B l C ->
  list_sequent Γ (Arr A B) (u :: l) C.

Hint Constructors sequent list_sequent : core.

Scheme sim_sequent_ind := Induction for sequent Sort Prop
  with sim_list_sequent_ind := Induction for list_sequent Sort Prop.

Combined Scheme mut_sequent_ind from sim_sequent_ind, sim_list_sequent_ind.
