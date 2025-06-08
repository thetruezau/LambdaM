Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import LambdaM Canonical IsCanonical.

Import ListNotations.

(* Projecção de λm em λc *)

Fixpoint h (t: LambdaM.term) : Canonical.term :=
  match t with
  | Var x => Vari x
  | Lam t' => Lamb (h t')
  | mApp v u l => (h v)@(h u, map h l)
  end.

(* Injecção de λc em λm *)

Fixpoint i (t: Canonical.term) : LambdaM.term :=
  match t with
  | Vari x => Var x
  | Lamb t' => Lam (i t')
  | VariApp x u l => mApp (Var x) (i u) (map i l)
  | LambApp v u l => mApp (Lam (i v)) (i u) (map i l)
  end.

(* i e h são bijecções *)
(* ------------------- *)

Proposition inversion1 : forall (t: LambdaM.term), is_canonical t -> i (h t) = t.
Proof.
  intros t it.
  induction it using sim_is_canonical_ind
    with (P0 := fun l (_: is_canonical_list l) => map i (map h l) = l) ;
    asimpl ; repeat f_equal ; auto.
Qed.

Proposition inversion2 : forall (t: Canonical.term), h (i t) = t.
Proof.
  intros t.
  induction t using Canonical.sim_term_ind ; asimpl ; repeat f_equal ; auto.
  all: induction H ; asimpl ; f_equal ; auto.
Qed.

(* Alguns lemas para auxiliar os resultados seguintes *)
(* -------------------------------------------------- *)

Local Hint Resolve up_subst_is_closed : core.

Lemma app_subst_pres :
  forall t u l σ, (t@(u,l)).[σ] = t.[σ]@(u.[σ], l..[σ]).
Proof.
  destruct t ; intros ; asimpl.
  - reflexivity.
  - reflexivity.
  - destruct (σ x) ; asimpl ; f_equal.
    + apply map_app.
    + apply map_app.
    + repeat rewrite<- app_assoc. f_equal.
      rewrite<- app_comm_cons. f_equal. apply map_app. 
    + repeat rewrite<- app_assoc. f_equal.
      rewrite<- app_comm_cons. f_equal. apply map_app.
  - destruct (t.[up σ]) ; asimpl ; f_equal.
    + apply map_app.
    + apply map_app.
    + repeat rewrite<- app_assoc. f_equal. apply map_app. 
    + repeat rewrite<- app_assoc. f_equal. apply map_app.
Qed.

Lemma h_ren_pres :
  forall t ξ, h t.[ren ξ] = (h t).[ren ξ].
Proof.
  induction t using LambdaM.sim_term_ind ; intros ; asimpl.
  - reflexivity.
  - f_equal. trivial.
  - rewrite app_subst_pres. f_equal ; trivial.
    + induction H ; asimpl ; msimpl in IHForall ; f_equal ; trivial.
Qed.

Local Hint Resolve h_ren_pres : core.

Lemma h_app_pres :
  forall t u l, h (app t u l) = (h t)@(h u, map h l).
Proof.
  destruct t ; intros ; try reflexivity.
  - asimpl. destruct (h t1) ; asimpl in *.
    + f_equal. apply map_app.
    + f_equal. apply map_app.
    + f_equal. repeat rewrite<- app_assoc. f_equal.
      rewrite map_app. asimpl. reflexivity.
    + f_equal. repeat rewrite<- app_assoc. f_equal.
      rewrite map_app. asimpl. reflexivity.
Qed.

Lemma i_app_pres :
  forall t u l, i (t@(u,l)) = app (i t) (i u) (map i l).
Proof.
  intros t u l.
  induction t using Canonical.sim_term_ind ; asimpl ; f_equal ; apply map_app.
Qed.

Lemma i_ren_pres :
  forall t, forall ξ, i t.[ren ξ] = (i t).[ren ξ].
Proof.
  induction t using Canonical.sim_term_ind ; intros ; asimpl ;
    repeat rewrite up_upren_internal ; simpl ; f_equal ; auto.
  all: induction H ; asimpl ; f_equal ; auto.
Qed.

Local Hint Resolve i_ren_pres : core.

Lemma h_simple_subst : forall u, ((h u) .: ids) = (u .: ids) >>> h.
Proof. intro. f_ext. destruct x ; reflexivity. Qed.

Lemma i_simple_subst : forall u, ((i u) .: ids) = (u .: ids) >>> i.
Proof. intro u. f_ext. destruct x ; reflexivity. Qed.

(* As bijecções preservam a substituição *)
(* ------------------------------------- *)

Theorem h_subst_pres :
  forall (t: LambdaM.term), is_canonical t ->
             forall σ, is_canonical_subst σ -> h (t.{σ}) = (h t).[σ >>> h].
Proof.
  intros t it.
  induction it using sim_is_canonical_ind
    with (P0 := fun l (_: is_canonical_list l) => forall σ, is_canonical_subst σ -> map h l..{σ} = (map h l)..[σ >>> h]) ; intros ; asimpl ; trivial.
  - f_equal. rewrite IHit ; auto.
    f_equal. f_ext. destruct x ; asimpl ; auto.
  - rewrite h_app_pres.
    + f_equal ; auto.
  - f_equal ; auto. rewrite IHit1 ; auto.
    f_equal. f_ext. destruct x ; asimpl ; auto.
  - f_equal ; auto.
Qed.

Theorem i_subst_pres :
  forall (t: Canonical.term), forall σ, i t.[σ] = (i t).{σ >>> i}.
Proof.
  induction t using Canonical.sim_term_ind ; intros ; asimpl ; repeat f_equal ; auto.
  - rewrite IHt. f_equal. f_ext.
    destruct x ; asimpl ; auto.
  - rewrite i_app_pres. f_equal ; auto.
    + induction H ; asimpl ; f_equal ; auto.
  - rewrite IHt1. f_equal. f_ext.
    destruct x ; asimpl ; auto.
  - induction H ; asimpl ; f_equal ; auto.
Qed.

(* As bijecções preservam a relação de um passo *)
(* -------------------------------------------- *)

Theorem h_step_pres :
  forall (t t': LambdaM.term), step_can t t' -> is_canonical t -> Canonical.step (h t) (h t').
Proof.
  pose Canonical.step_is_compatible as H. destruct H.  
  
  intros t t' H.
  induction H using LambdaM.sim_comp_ind
    with (P0 := fun l1 l2 (_: step_can' l1 l2) => is_canonical_list l1 -> Canonical.step' (map h l1) (map h l2)) ; intro it ; inversion it ; subst ; asimpl ; auto.
  
  - (* temos hipóteses que são absurdas *)
    inversion H. inversion H0 ; inversion H5.
  - inversion H ; subst ; asimpl.
    + constructor.
      apply cLam in H3. apply IHcomp in H3. inversion H3 ; trivial.
      * (* temos hipóteses que são absurdas *)
        inversion H0 ; asimpl in H7 ; inversion H7.
    + (* temos hipóteses que são absurdas *)
      inversion H0 ; inversion H1.
  - (* temos hipóteses que são absurdas *)
    inversion b ; inversion H.
  - (* temos hipóteses que são absurdas *) 
    inversion b ; inversion H0.
  - (* temos hipóteses que são absurdas *)
    inversion b ; inversion H1.
  - assert (cons_lemma :
             forall u, is_canonical u -> is_canonical_subst (u .: ids)).
    { intro. autounfold. destruct x ; asimpl ; trivial. }
      
    inversion H1 ; subst ; asimpl.
    + inversion b ; subst.
      * constructor. left.
        inversion H2 ; subst. constructor.
        rewrite h_simple_subst. apply h_subst_pres ; auto.
      * (* temos hipóteses que são absurdas *)
        inversion H2.
    + inversion b ; subst.
      * (* temos hipóteses que são absurdas *)
        inversion H4.
      * constructor. right.
        inversion H4 ; subst. constructor.
        rewrite h_app_pres ; asimpl ; trivial.
        f_equal ; trivial.
        ** rewrite h_simple_subst. apply h_subst_pres ; auto.
Qed.

Theorem i_step_pres :
  forall (t t': Canonical.term), Canonical.step t t' -> step_can (i t) (i t').
Proof.
  intros t t' H.
  induction H using Canonical.sim_comp_ind
    with (P0 := fun l1 l2 (_: Canonical.step' l1 l2) => step_can' (map i l1) (map i l2)) ; asimpl ; try (now constructor ; assumption).
  - constructor. constructor. assumption.
  - inversion b.
    + inversion H ; subst ; asimpl.
      constructor. left. constructor.
      rewrite i_simple_subst. apply i_subst_pres.
    + inversion H ; subst ; asimpl.
      constructor. right. constructor.
      rewrite i_app_pres. f_equal ; asimpl ; trivial.
      rewrite i_simple_subst. apply i_subst_pres.
Qed.

(* Lemas adicionais sobre as bijecções *)
(* ----------------------------------- *)

Lemma i_image_is_canonical : forall t, is_canonical (i t).
Proof.
  intro t.
  induction t using Canonical.sim_term_ind ; asimpl ; auto.
  - constructor.
    + assumption.
    + induction H ; asimpl ; constructor ; assumption.
  - constructor.
    + assumption.
    + assumption.
    + induction H ; asimpl ; constructor ; assumption.
Qed.
