From Coq Require Import List.
From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

Require Import Autosubst.Autosubst.
Require Import LambdaM Canonical IsCanonical CanonicalIsomorphism.

Import ListNotations.

Proposition multistep_trans (A: Type) (R: relation A):
  forall x y z, clos_refl_trans_1n _ R x y -> clos_refl_trans_1n _ R y z ->
           clos_refl_trans_1n _ R x z.
Proof.                                                  
  intros.
  induction H ; try easy.
  - apply rt1n_trans with y ; try easy.
    + now apply IHclos_refl_trans_1n. 
Qed.

Lemma mApp_multistep_to_app :
  forall t u l, LambdaM.multistep (mApp t u l) (app t u l).
Proof.
  destruct t ; intros ; asimpl ; try apply rt1n_refl.
  - apply rt1n_trans with (mApp t1 t2 (l ++ u :: l0)) ; try apply rt1n_refl.
    + constructor. right. now constructor. 
Qed.

Local Hint Resolve up_subst_is_closed : core.

Lemma two_subst_multistep :
  forall t, is_canonical t -> forall σ, is_canonical_subst σ -> LambdaM.multistep t.[σ] t.{σ}.
Proof.
  pose LambdaM.multistep_is_compatible as H. destruct H.

  intros t it.  
  induction it using sim_is_canonical_ind
    with (P0 := fun l (_: is_canonical_list l) => forall σ, is_canonical_subst σ -> LambdaM.multistep' l..[σ] l..{σ}) ; intros ; asimpl ;
    try constructor ; auto.

  - eapply multistep_trans ; fold LambdaM.multistep ; eauto.
    eapply multistep_trans ; fold LambdaM.multistep ; eauto.
    apply mApp_multistep_to_app.

  - eapply multistep_trans ; fold LambdaM.multistep ; eauto.
    eapply multistep_trans ; fold LambdaM.multistep ; eauto.
    
  - eapply multistep_trans ; fold LambdaM.multistep' ; eauto.
Qed.

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
      apply rt1n_trans with ((i t0).[(i u)/]).
      * unfold LambdaM.step. constructor. left. left.
        now constructor. 
      * rewrite (proj1 i_subst_pres). rewrite<- i_simple_subst.
        apply two_subst_multistep.
        ** apply i_image_is_canonical.
        ** autounfold.
           destruct x ; asimpl ; try easy.
           *** apply i_image_is_canonical.

    (* reproduzir Beta2 em λm *)
    + inversion Beta2 ; subst. asimpl.
      apply rt1n_trans with (mApp ((i t0).[(i u)/]) (i v) (map i l)).
      * unfold LambdaM.step. constructor. left. right.
        now constructor. 
      * apply multistep_trans with (mApp (i t0.[u/]) (i v) (map i l)).
        ** apply comp_mApp1.
           rewrite (proj1 i_subst_pres).
           rewrite<- i_simple_subst.
           apply two_subst_multistep.
           *** apply i_image_is_canonical.
           *** autounfold.
               destruct x ; asimpl ; try easy.
               **** apply i_image_is_canonical.
        ** destruct (t0.[u/]) ; asimpl in * ; subst ; try apply rt1n_refl.
           *** apply rt1n_trans with (mApp (Var x) (i t) (map i (l0 ++ v :: l))) ; try easy.
               **** constructor. right. constructor. now apply map_app.
               **** constructor.
           *** apply rt1n_trans with (mApp (Lam (i t)) (i t1) (map i (l0 ++ v :: l))).
               **** constructor. right. constructor. apply map_app.
               **** constructor.
Qed.

Lemma h_subst_eq :
  (forall (t: LambdaM.term) σ, h t.[σ] = (h t).[σ >>> h])
  /\
  (forall (l: list LambdaM.term) σ, map h l..[σ] = (map h l)..[σ >>> h]).
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; f_equal ; try easy.
  - now rewrite<- h_up_subst.
  - rewrite H, H0, H1. now rewrite app_subst_pres.
Qed.

Lemma conservativeness2 :
  (forall (t t': LambdaM.term), LambdaM.step t t' -> Canonical.multistep (h t) (h t'))
  /\
  (forall (l l': list LambdaM.term), LambdaM.step' l l' -> Canonical.multistep' (map h l) (map h l')).
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
        apply rt1n_trans with ((h t0).[h u/]).
        ** constructor. left. now constructor. 
        ** rewrite (proj1 h_subst_eq).
           rewrite h_simple_subst. constructor.
      * inversion Beta2 ; subst ; asimpl.
        apply rt1n_trans with ((h t0).[h u/]@(h v, map h l)).
        ** constructor. right. now constructor. 
        ** apply multistep_comp_app1.
           rewrite (proj1 h_subst_eq).
           rewrite h_simple_subst. constructor.

    (* h colapsa passos H *)
    + inversion H ; subst ; asimpl.
      (* aqui talvez fosse importante um lema! *)
      destruct (h t0) ; asimpl ; rewrite map_app ; try constructor.
      * rewrite<- app_assoc. asimpl. constructor.
      * rewrite<- app_assoc. asimpl. constructor.
Qed.

(* Teorema da conservatividade *)
(* --------------------------- *)

Theorem conservativeness :
  forall t t', Canonical.multistep t t' <-> LambdaM.multistep (i t) (i t').
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
    + apply multistep_trans with (h t2) ; try easy.
      * now apply conservativeness2. 
Qed.
