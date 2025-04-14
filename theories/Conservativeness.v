Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import LambdaM Canonical IsCanonical CanonicalIsomorphism.

Import ListNotations.

Proposition multistep_trans (A: Type) (R: relation A):
  forall x y z, clos_refl_trans_1n _ R x y -> clos_refl_trans_1n _ R y z ->
           clos_refl_trans_1n _ R x z.
Proof.                                                  
  intros. induction H.
  - assumption.
  - apply rt1n_trans with y.
    + assumption.
    + apply IHclos_refl_trans_1n. assumption.
Qed.

Lemma two_subst_multistep :
  forall t, is_canonical t -> forall σ, is_canonical_subst σ -> LambdaM.multistep t.[σ] t.{σ}.
Proof.
  pose LambdaM.multistep_is_compatible as H. destruct H.

  intros t it.
  induction it using sim_is_canonical_ind
    with (P0 := fun l (_: is_canonical_list l) => forall σ, is_canonical_subst σ -> LambdaM.multistep' l..[σ] l..{σ}) ; intros ; asimpl ; try constructor ; auto.
  - destruct (σ x) as [x0 | t | v u' l'] ; asimpl.
    + apply multistep_trans with (mApp (Var x0) u.{σ} l..[σ]) ;
        fold LambdaM.multistep ; auto.
    + apply multistep_trans with (mApp (Lam t) u.{σ} l..[σ]) ;
        fold LambdaM.multistep ; auto.
    + apply rt1n_trans with (mApp v u' (l' ++ u.[σ] :: l..[σ])).
      * constructor. right. constructor. reflexivity.
      * apply comp_mApp3.
        induction l' ; asimpl ; fold LambdaM.multistep' ; auto.
        ** apply multistep_trans with (u.{σ} :: l..[σ]) ;
             fold LambdaM.multistep' ; auto.
  - apply multistep_trans with (mApp (Lam t.{up σ}) u.[σ] l..[σ]) ;
      fold LambdaM.multistep ; auto.
    + apply multistep_trans with (mApp (Lam t.{up σ}) u.{σ} l..[σ]) ;
        fold LambdaM.multistep ; auto.
  - apply multistep_trans with (u.{σ} :: l..[σ]) ;
      fold LambdaM.multistep' ; auto.
Qed.

Lemma conservativeness1 :
  forall (t t': λc), Canonical.step t t' -> LambdaM.multistep (i t) (i t').
Proof.
  pose LambdaM.multistep_is_compatible as H. destruct H.
  
  intros t t' s.
  induction s using Canonical.sim_comp_ind
    with (P0 := fun l l' (_: Canonical.step' l l') => LambdaM.multistep' (map i l) (map i l')) ; asimpl ; auto.
  - inversion b as [Beta1 | Beta2].

    (* reproduzir Beta1 em λm *)
    + inversion Beta1 ; subst. asimpl.
      apply rt1n_trans with ((i t0).[(i u)/]).
      * unfold LambdaM.step. constructor. left. left.
        constructor. reflexivity.
      * rewrite i_subst_pres. rewrite<- i_simple_subst.
        apply two_subst_multistep.
        ** apply i_image_is_canonical.
        ** autounfold.
           destruct x ; asimpl ; [apply i_image_is_canonical | constructor].

    (* reproduzir Beta2 em λm *)
    + inversion Beta2 ; subst. asimpl.
      apply rt1n_trans with (mApp ((i t0).[(i u)/]) (i v) (map i l)).
      * unfold LambdaM.step. constructor. left. right.
        constructor. reflexivity.
      * apply multistep_trans with (mApp (i t0.[u/]) (i v) (map i l)).
        ** apply comp_mApp1. rewrite i_subst_pres. rewrite<- i_simple_subst.
           apply two_subst_multistep.
           *** apply i_image_is_canonical.
           *** autounfold.
               destruct x ; asimpl ; [apply i_image_is_canonical | constructor].
        ** destruct (t0.[u/]) ; asimpl in * ; subst ; try apply rt1n_refl.
           *** apply rt1n_trans with (mApp (Var x) (i λ) (map i (l0 ++ v :: l))).
               **** constructor. right. constructor. apply map_app.
               **** constructor.
           *** apply rt1n_trans with (mApp (Lam (i t)) (i λ) (map i (l0 ++ v :: l))).
               **** constructor. right. constructor. apply map_app.
               **** constructor.
Qed.

Lemma h_subst_eq :
  forall (t: λm) σ, h t.[σ] = (h t).[σ >>> h].
Proof.
  induction t using sim_λm_ind ; intros ; asimpl.
  - reflexivity.
  - f_equal. rewrite IHt. f_equal.
    f_ext. induction x ; asimpl ; trivial. apply h_ren_pres.
  - assert (IHl : map h l..[σ] = (map h l)..[σ >>> h]).
    { induction H ; asimpl ; f_equal ; auto. }
    rewrite IHt1, IHt2, IHl. rewrite app_subst_pres. reflexivity.    
Qed.

Lemma conservativeness2 :
  forall (t t': λm), LambdaM.step t t' -> Canonical.multistep (h t) (h t'). 
Proof.
  pose Canonical.multistep_is_compatible as H. destruct H.
  
  intros t t' s.
  induction s using LambdaM.sim_comp_ind
    with (P0 := fun l l' (_: LambdaM.step' l l') => Canonical.multistep' (map h l) (map h l')) ; asimpl ; auto.
  - apply multistep_comp_app1. assumption.
  - apply multistep_comp_app2. assumption.
  - apply multistep_comp_app3. assumption.
  - inversion b as [Beta | H].

    (* h preserva passos Beta *)
    + inversion Beta as [Beta1 | Beta2].
      * inversion Beta1 ; subst ; asimpl.
        apply rt1n_trans with ((h t0).[h u/]).
        ** constructor. left. constructor. reflexivity.
        ** rewrite h_subst_eq. rewrite h_simple_subst. constructor.
      * inversion Beta2 ; subst ; asimpl.
        apply rt1n_trans with ((h t0).[h u/]@(h v, map h l)).
        ** constructor. right. constructor. reflexivity.
        ** apply multistep_comp_app1.
           rewrite h_subst_eq. rewrite h_simple_subst. constructor.

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
  forall (t t': λc), Canonical.multistep t t' <-> LambdaM.multistep (i t) (i t').
Proof.
  split.
  - induction 1 as [| t1 t2 t3].
    + constructor.
    + apply multistep_trans with (i t2).
      * apply conservativeness1. assumption.
      * assumption.
  - intro H.
    rewrite<- bijection2 with t.
    rewrite<- bijection2 with t'.
    induction H as [| t1 t2 t3].
    + constructor.
    + apply multistep_trans with (h t2).
      * apply conservativeness2. assumption.
      * assumption.
Qed.
