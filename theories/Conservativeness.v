From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
Require Import MyRelations.

From Autosubst Require Import Autosubst.
Require Import LambdaM Canonical.
Require Import IsCanonical CanonicalIsomorphism.

From Coq Require Import List.
Import ListNotations.

Lemma conservativeness1 :
  (forall (t t': Canonical.term), Canonical.step t t' -> LambdaM.multistep (i t) (i t'))
  /\
  (forall l l', Canonical.step' l l' -> LambdaM.multistep' (map i l) (map i l')).
Proof.
  pose LambdaM.multistep_is_compatible as H. destruct H.

  apply Canonical.mut_comp_ind ; intros ; asimpl ; auto.

  - inversion b as [Beta1 | Beta2].

    (* reproduzir Beta1 em λm *)
    + inversion Beta1 ; subst. asimpl.
      apply rt1n_trans with (i t0).[(i u)/].
      * unfold LambdaM.step. constructor. left. now left.
      * rewrite (proj1 i_subst_pres).
        rewrite i_subst_rw.
        apply multistep_H_inclusion.        
        apply h_is_multistep_H.
        
    (* reproduzir Beta2 em λm *)
    + inversion Beta2 ; subst. asimpl.
      apply rt1n_trans
        with (mApp ((i t0).[(i u)/]) (i v) (map i l)).
      * constructor. left. now right. 
      * apply multistep_trans
          with (mApp (i t0.[u/]) (i v) (map i l)).
        ** apply comp_mApp1.
           rewrite (proj1 i_subst_pres).
           rewrite i_subst_rw.
           apply multistep_H_inclusion.        
           apply h_is_multistep_H.
        ** rewrite i_app_comm. 
           apply multistep_H_inclusion.
           apply capp_is_multistep_H.
Qed.

Lemma can_app_comm t u u' l l' :
  (t @(u, map p l)) @(p u', map p l') = 
    t@(u, map p (l ++ u' :: l')).
Proof.
  destruct t ; simpl ; rewrite map_app ;
    try rewrite<- app_assoc ; now simpl.
Qed.

Lemma conservativeness2 :
  (forall (t t': LambdaM.term), LambdaM.step t t' -> Canonical.multistep (p t) (p t'))
  /\
  (forall (l l': list LambdaM.term), LambdaM.step' l l' -> Canonical.multistep' (map p l) (map p l')).
Proof.
  pose Canonical.multistep_is_compatible as H. destruct H.

  apply LambdaM.mut_comp_ind ; intros ; asimpl ; auto.
  - now apply multistep_comp_app1. 
  - now apply multistep_comp_app2. 
  - now apply multistep_comp_app3. 
    
  - inversion b as [Beta | H].

    (* h preserva passos Beta *)
    + inversion Beta as [Beta1 | Beta2].
      * inversion Beta1 ; subst ; asimpl.
        apply rt1n_trans with ((p t0).[p u/]).
        ** constructor. left. now constructor. 
        ** rewrite (proj1 p_subst_pres).
           rewrite p_subst_rw. constructor.
      * inversion Beta2 ; subst ; asimpl.
        apply rt1n_trans with ((p t0).[p u/]@(p v, map p l)).
        ** constructor. right. now constructor. 
        ** apply multistep_comp_app1.
           rewrite (proj1 p_subst_pres).
           rewrite p_subst_rw. constructor.

    (* h colapsa passos H *)
    + inversion H ; subst ; asimpl.
      rewrite can_app_comm. constructor.
Qed.

(* Teorema da conservatividade *)
(* --------------------------- *)

Theorem conservativeness :
  forall t t', Canonical.multistep t t' <->
           LambdaM.multistep (i t) (i t').
Proof.
  split.
  - intro H.
    induction H as [| t1 t2 t3].
    + constructor.
    + apply multistep_trans with (i t2) ; try easy.
      * now apply conservativeness1. 
  - intro H.
    rewrite<- (proj1 inversion2) with t.
    rewrite<- (proj1 inversion2) with t'.
    induction H as [| t1 t2 t3].
    + constructor.
    + apply multistep_trans with (p t2) ; try easy.
      * now apply conservativeness2. 
Qed.
