From Coq Require Import List.
From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
Require Import MyRelations.

Require Import Autosubst.Autosubst.
Require Import LambdaM Canonical.
Require Import IsCanonical CanonicalIsomorphism.

Import ListNotations.

Lemma conservativeness1 :
  (forall (t t': Canonical.term), Canonical.step t t' -> LambdaM.multistep (ι t) (ι t'))
  /\
  (forall l l', Canonical.step' l l' -> LambdaM.multistep' (map ι l) (map ι l')).
Proof.
  pose LambdaM.multistep_is_compatible as H. destruct H.

  apply Canonical.mut_comp_ind ; intros ; asimpl ; auto.

  - inversion b as [Beta1 | Beta2].

    (* reproduzir Beta1 em λm *)
    + inversion Beta1 ; subst. asimpl.
      apply rt1n_trans with (ι t0).[(ι u)/].
      * unfold LambdaM.step. constructor. left. left.
        now constructor. 
      * apply multistep_H_inclusion.
        rewrite ι_subst_rw. apply ι_subst_pres.

    (* reproduzir Beta2 em λm *)
    + inversion Beta2 ; subst. asimpl.
      apply rt1n_trans with (mApp ((ι t0).[(ι u)/]) (ι v) (map ι l)).
      * constructor. left. right. now constructor. 

      * apply multistep_trans with (mApp (ι t0.[u/]) (ι v) (map ι l)).
        ** apply comp_mApp1.
           apply multistep_H_inclusion.
           rewrite ι_subst_rw. apply ι_subst_pres.

        ** rewrite ι_app_pres. 
           apply multistep_H_inclusion.
           apply app_is_multistep_H.
Qed.

Lemma conservativeness2 :
  (forall (t t': LambdaM.term), LambdaM.step t t' -> Canonical.multistep (π t) (π t'))
  /\
  (forall (l l': list LambdaM.term), LambdaM.step' l l' -> Canonical.multistep' (map π l) (map π l')).
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
        apply rt1n_trans with ((π t0).[π u/]).
        ** constructor. left. now constructor. 
        ** rewrite (proj1 π_subst_pres).
           rewrite π_subst_rw. constructor.
      * inversion Beta2 ; subst ; asimpl.
        apply rt1n_trans with ((π t0).[π u/]@(π v, map π l)).
        ** constructor. right. now constructor. 
        ** apply multistep_comp_app1.
           rewrite (proj1 π_subst_pres).
           rewrite π_subst_rw. constructor.

    (* h colapsa passos H *)
    + inversion H ; subst ; asimpl.
      (* aqui talvez fosse importante um lema! *)
      destruct (π t0) ; asimpl ;
        rewrite map_app ; try constructor.
      * rewrite<- app_assoc. asimpl. constructor.
      * rewrite<- app_assoc. asimpl. constructor.
Qed.

(* Teorema da conservatividade *)
(* --------------------------- *)

Theorem conservativeness :
  forall t t', Canonical.multistep t t' <-> LambdaM.multistep (ι t) (ι t').
Proof.
  split.
  - intro H.
    induction H as [| t1 t2 t3].
    + constructor.
    + apply multistep_trans with (ι t2) ; try easy.
      * now apply conservativeness1. 
  - intro H.
    rewrite<- (proj1 inversion2) with t.
    rewrite<- (proj1 inversion2) with t'.
    induction H as [| t1 t2 t3].
    + constructor.
    + apply multistep_trans with (π t2) ; try easy.
      * now apply conservativeness2. 
Qed.
