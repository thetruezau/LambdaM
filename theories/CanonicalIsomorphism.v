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

Proposition inversion1 :
  (forall (t: LambdaM.term), is_canonical t -> i (h t) = t)
  /\
  (forall (l: list LambdaM.term), is_canonical_list l ->
                             map i (map h l) = l).
Proof.
  apply mut_is_canonical_ind ; intros ; asimpl ;
    repeat f_equal ; auto.
Qed.  

Proposition inversion2 :
  (forall (t: Canonical.term), h (i t) = t)
  /\
  (forall (l: list Canonical.term), map h (map i l) = l).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ;
    repeat f_equal ; auto.
Qed.

(* Alguns lemas para auxiliar os resultados seguintes *)
(* -------------------------------------------------- *)

Lemma app_subst_pres :
  forall t u l σ, (t@(u,l)).[σ] = t.[σ]@(u.[σ], l..[σ]).
Proof.
  destruct t ; intros ; asimpl ; try easy.
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

Lemma h_app_pres :
  forall t u l, h (app t u l) = (h t)@(h u, map h l).
Proof.
  destruct t ; intros ; try easy.
  - asimpl. destruct (h t1) ; asimpl in *.
    + f_equal. apply map_app.
    + f_equal. apply map_app.
    + f_equal. repeat rewrite<- app_assoc. f_equal.
      rewrite map_app. now asimpl.
    + f_equal. repeat rewrite<- app_assoc. f_equal.
      rewrite map_app. now asimpl. 
Qed.

Lemma i_app_pres :
  forall t u l, i (t@(u,l)) = app (i t) (i u) (map i l).
Proof.
  intros t u l.
  destruct t ; asimpl ; f_equal ; apply map_app.
Qed.

Lemma h_ren_pres :
  (forall t ξ, h t.[ren ξ] = (h t).[ren ξ])
  /\
  (forall l ξ, map h (l..[ren ξ]) = (map h l)..[ren ξ]).
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; auto.
  - now f_equal.
  - rewrite app_subst_pres. now f_equal.
  - now f_equal.
Qed.

Lemma i_ren_pres :
  (forall t, forall ξ, i t.[ren ξ] = (i t).[ren ξ])
  /\
  (forall l ξ, map i (l..[ren ξ]) = (map i l)..[ren ξ]).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; auto.
  - now f_equal.
  - simpl. now f_equal.
  - now repeat f_equal.
  - now f_equal.
Qed.

Lemma h_up_subst σ : up σ >>> h = up (σ >>> h).
Proof.
  f_ext. destruct x ; asimpl ; try easy. 
  - apply h_ren_pres.
Qed.

Lemma i_up_subst σ : up σ >>> i = up (σ >>> i).
Proof.
  f_ext. destruct x ; asimpl ; try easy. 
  - apply i_ren_pres.
Qed.

(* As bijecções preservam a substituição *)
(* ------------------------------------- *)

Theorem h_subst_pres:
  (forall t, is_canonical t -> forall σ, is_canonical_subst σ -> h (t.{σ}) = (h t).[σ >>> h])
  /\
    (forall l, is_canonical_list l -> forall σ, is_canonical_subst σ -> map h (l..{σ}) = (map h l)..[σ >>> h])

.
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; try easy.
  - f_equal. rewrite H.
    + now rewrite h_up_subst.
    + now inversion H0.
    + now apply up_subst_is_closed.
      
  - inversion H2 ; subst.
    + rewrite h_app_pres, app_subst_pres. f_equal ; auto.
    + rewrite h_app_pres, app_subst_pres. f_equal ; auto.

  - inversion H1 ; subst.
    f_equal ; auto.
Qed.

Theorem i_subst_pres :
  (forall t σ, i t.[σ] = (i t).{σ >>> i})
  /\
  (forall l σ, map i l..[σ] = (map i l)..{σ >>> i}).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ;
    repeat f_equal ; auto.
  - now rewrite<- i_up_subst. 
  - rewrite i_app_pres. now f_equal.
  - now rewrite<- i_up_subst. 
Qed.

(* As bijecções preservam a relação de um passo *)
(* -------------------------------------------- *)

Lemma h_simple_subst u : (h u).:ids = (u.:ids)>>>h.
Proof. autosubst. Qed.

Theorem h_step_pres :
  (forall (t t': LambdaM.term), step_can t t' -> is_canonical t -> Canonical.step (h t) (h t'))
  /\ 
  (forall l l', step_can' l l' -> is_canonical_list l -> Canonical.step'(map h l) (map h l')). 
Proof.
  pose Canonical.step_is_compatible as H. destruct H.  
  pose Canonical.step_comp_app1.
  pose Canonical.step_comp_app2.
  pose Canonical.step_comp_app3.
    
  apply LambdaM.mut_comp_ind ; intros ; asimpl ;
    try inversion H0 ; subst ; auto.

  - inversion b ; subst.
    * constructor. left.
      inversion H0 ; subst. asimpl. constructor.
      inversion H ; subst.
      rewrite h_simple_subst.
      rewrite (proj1 h_subst_pres) ; try easy.
      ** autounfold. now destruct x ; asimpl.
        
    * constructor. right.
      inversion H0 ; subst. asimpl. constructor.
      inversion H ; subst.            
      rewrite h_app_pres. asimpl. f_equal.
      rewrite h_simple_subst.
      rewrite (proj1 h_subst_pres) ; try easy.
      ** autounfold. now destruct x ; asimpl.
Qed.

Lemma i_simple_subst u : (i u).:ids = (u.:ids)>>>i.
Proof. autosubst. Qed.

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

Lemma i_image_is_canonical :
  (forall t, is_canonical (i t))
  /\
  (forall l, is_canonical_list (map i l)).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; auto.
Qed.
