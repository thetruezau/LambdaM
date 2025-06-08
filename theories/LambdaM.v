Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* Sintaxe *)
(* ------- *)

Inductive term: Type :=
| Var (x: var)
| Lam (t: {bind term})
| mApp (t: term) (u: term) (l: list term).

Section dedicated_induction_principle.
  Variable P : term -> Prop.

  Hypothesis HVar : forall x, P (Var x).
  Hypothesis HLam : forall t, P t -> P (Lam t).
  Hypothesis HmApp : forall t u l, P t -> P u -> Forall P l ->
                                   P (mApp t u l).

  Proposition sim_term_ind : forall t, P t.
  Proof.
    fix rec 1. destruct t.
    - apply HVar.
    - apply HLam. apply rec.
    - apply HmApp.
      + apply rec.
      + apply rec.
      + assert (forall l, Forall P l). fix rec' 1. destruct l0.
        * apply Forall_nil.
        * apply Forall_cons ; [ apply rec | apply rec' ].
        * apply H.
  Qed.
End dedicated_induction_principle.

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

Theorem clos_refl_trans_pres_comp :
  forall R R', is_compatible R R' ->
          is_compatible (clos_refl_trans_1n _ R) (clos_refl_trans_1n _ R').
Proof.
  intros. destruct H. 
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

Hint Unfold step step': core.

Proposition step_is_compatible : is_compatible step step'.
Proof.
  split ; autounfold ; intros ; constructor ; assumption.
Qed.

Definition multistep := clos_refl_trans_1n _ step.
Definition multistep' := clos_refl_trans_1n _ step'.

Hint Unfold multistep multistep': core.

Proposition multistep_is_compatible :
  is_compatible multistep multistep'.
Proof.
  apply clos_refl_trans_pres_comp. apply step_is_compatible.
Qed.  

Section StepSubstitution.

  Lemma mmap_append (l1 l2: list term) (f: term -> term) :
    mmap f (l1 ++ l2) = (mmap f l1) ++ (mmap f l2).
  Proof.
    induction l1 ; asimpl ; try rewrite IHl1 ; auto.
  Qed.

  Local Hint Resolve mmap_append : core.

  Lemma step_subst :
    forall s t, step s t -> forall σ, step s.[σ] t.[σ].
  Proof.
    intros s t H.
    induction H using sim_comp_ind
      with (P0 := fun l l' (_: step' l l') => forall σ, step' l..[σ] l'..[σ]) ;
      intros ; autounfold ; asimpl ; constructor ; try apply IHcomp.
    
    - destruct b as [Beta | H].
      + destruct Beta as [Beta1 | Beta2 ].
        * induction Beta1. subst. left. left. constructor. autosubst.
        * induction Beta2. subst. left. right. constructor. autosubst.
      + induction H. subst. right. constructor. auto.
  Qed.

End StepSubstitution.

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
