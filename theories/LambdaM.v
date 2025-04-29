Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* Sintaxe *)
(* ------- *)

Inductive λm: Type :=
| Var (x: var)
| Lam (t: {bind λm})
| mApp (t: λm) (u: λm) (l: list λm).

Hint Constructors λm : core.

Section simultaneous_induction_principle.
  Variable P : λm -> Prop.

  Hypothesis HVar : forall x, P (Var x).
  Hypothesis HLam : forall t, P t -> P (Lam t).
  Hypothesis HmApp : forall t u l, P t -> P u -> Forall P l ->
                                   P (mApp t u l).

  Proposition sim_λm_ind : forall t, P t.
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
End simultaneous_induction_principle.

(* Substituição *)
(* ------------ *)

Instance Ids_λm : Ids λm. derive. Defined.
Instance Rename_λm : Rename λm. derive. Defined.
Instance Subst_λm : Subst λm. derive. Defined.
Instance SubstLemmas_λm : SubstLemmas λm. derive. Defined.

(* Definição de compatibilidade em λm *)
(* ---------------------------------- *)

Section Compatibilty.

  Variable base : relation λm.
  
  Inductive comp : relation λm :=
  | Comp_Lam (t t': {bind λm}) : comp t t' ->
                                 comp (Lam t) (Lam t')
  | Comp_mApp1 t t' u l : comp t t' ->
                          comp (mApp t u l) (mApp t' u l)
  | Comp_mApp2 t u u' l : comp u u' ->
                          comp (mApp t u l) (mApp t u' l)
  | Comp_mApp3 t u l l' : comp' l l' ->
                          comp (mApp t u l) (mApp t u l')
  | Step_Base t t' : base t t' -> comp t t'

  with comp' : relation (list λm) :=
  | Comp_Head u u' l : comp u u' -> comp' (u::l) (u'::l)
  | Comp_Tail u l l' : comp' l l' -> comp' (u::l) (u::l').

  Scheme sim_comp_ind := Induction for comp Sort Prop
    with sim_comp_ind' := Induction for comp' Sort Prop.

End Compatibilty.

Section IsCompatible.

  Variable R : relation λm.
  Variable R' : relation (list λm).

  Record is_compatible := {
      comp_lam : forall t t': {bind λm}, R t t' -> R (Lam t) (Lam t') ;
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

Inductive β1: relation λm :=
| Step_Beta1 (t: {bind λm}) (t' u: λm) :
  t' = t.[u .: ids] -> β1 (mApp (Lam t) u []) t'.

Inductive β2: relation λm :=
| Step_Beta2 (t: {bind λm}) (t' u v: λm) l :
  t' = t.[u .: ids] -> β2 (mApp (Lam t) u (v::l)) (mApp t' v l).

Inductive H: relation λm :=       
| Step_H (t u u': λm) l l' l'' :
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

  Lemma mmap_append (l1 l2: list λm) (f: λm -> λm) :
    mmap f (l1 ++ l2) = (mmap f l1) ++ (mmap f l2).
  Proof.
    induction l1 ; asimpl ; try rewrite IHl1 ; auto.
  Qed.

  Hint Resolve mmap_append : core.

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

