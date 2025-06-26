From Coq Require Import List.

From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
Require Import MyRelations.


Require Import Autosubst.Autosubst.
Require Import LambdaM Canonical.
Require Import IsCanonical.

Import ListNotations.

(* Injecção de λ⃗ em λm *)

Fixpoint ι (t: Canonical.term) : LambdaM.term :=
  match t with
  | Vari x => Var x
  | Lamb t' => Lam (ι t')
  | VariApp x u l => mApp (Var x) (ι u) (map ι l)
  | LambApp v u l => mApp (Lam (ι v)) (ι u) (map ι l)
  end.

(* Projecção de λm em λ⃗ *)

Fixpoint π (t: LambdaM.term) : Canonical.term :=
  match t with
  | Var x => Vari x
  | Lam t' => Lamb (π t')
  | mApp v u l => (π v)@(π u, map π l)
  end.

(* π e ι são bijecções *)
(* ------------------- *)

Proposition inversion1 :
  (forall (t: LambdaM.term), is_canonical t -> ι (π t) = t)
  /\
  (forall (l: list LambdaM.term), is_canonical_list l ->
                             map ι (map π l) = l).
Proof.
  apply mut_is_canonical_ind ;
    intros ; asimpl ; repeat f_equal ; auto.
Qed.  

Proposition inversion2 :
  (forall (t: Canonical.term), π (ι t) = t)
  /\
  (forall (l: list Canonical.term), map π (map ι l) = l).
Proof.
  apply Canonical.mut_term_ind ;
    intros ; asimpl ; repeat f_equal ; auto.
Qed.

(* Alguns lemas para auxiliar os resultados seguintes *)
(* -------------------------------------------------- *)

Lemma ι_app_pres t u l :
  ι t@(u,l) = app (ι t) (ι u) (map ι l).
Proof.
  destruct t ; asimpl ; f_equal ; apply map_app.
Qed.

Lemma π_app_pres t u l :
  π (app t u l) = (π t)@(π u, map π l).
Proof.
  destruct t ; try easy.
  - asimpl. destruct (π t1) ; asimpl in *.
    + now rewrite map_app.
    + now rewrite map_app.
    + f_equal. repeat rewrite<- app_assoc. f_equal.
      rewrite map_app. now asimpl.
    + f_equal. repeat rewrite<- app_assoc. f_equal.
      rewrite map_app. now asimpl. 
Qed.

(* Resultados para a preservacao da substituicao por ι *)
(* --------------------------------------------------- *)

Lemma ι_ren_pres :
  (forall t ξ, ι t.[ren ξ] = (ι t).[ren ξ])
  /\
  (forall l ξ, map ι l..[ren ξ] = (map ι l)..[ren ξ]).
Proof.
  apply Canonical.mut_term_ind ; intros ; try easy.
  - asimpl. rewrite H. autosubst.
  - simpl. now f_equal.
  - simpl. f_equal ; try easy.
    + asimpl. rewrite H. autosubst.
  - asimpl. now f_equal.
Qed.

Lemma ι_up_subst σ : up (σ >>> ι) = up σ >>> ι.
Proof.
  f_ext.
  destruct x ; asimpl ; try easy.
  - rewrite (proj1 ι_ren_pres). autosubst.
Qed.

Theorem ι_subst_pres :
  (forall t σ, multistep_H (ι t).[σ >>> ι] (ι t.[σ]))
  /\
  (forall l σ, multistep_H' (map ι l)..[σ >>> ι] (map ι l..[σ])).
Proof.
  pose multistep_H_is_compatible as i. destruct i.
  
  apply Canonical.mut_term_ind ; intros ; asimpl.
  - constructor.
  - apply comp_lam.
    + now rewrite ι_up_subst.

  - rewrite ι_app_pres. 
    apply multistep_trans
      with (mApp (ι (σ x)) (ι u.[σ]) (map ι l)..[σ >>> ι]).

    + now apply comp_mApp2.
        
    + apply multistep_trans
        with (mApp (ι (σ x)) (ι u.[σ]) (map ι l..[σ])).
      * now apply comp_mApp3.
      * now apply app_is_multistep_H.

  - apply multistep_trans
      with (mApp (Lam (ι t.[up σ])) (ι u).[σ >>> ι] (map ι l)..[σ >>> ι]).
    + apply comp_mApp1.
      * rewrite ι_up_subst. now apply comp_lam.
    + apply multistep_trans
        with (mApp (Lam (ι t.[up σ])) (ι u.[σ]) (map ι l)..[σ >>> ι]).
      * now apply comp_mApp2.
      * apply multistep_trans
          with (mApp (Lam (ι t.[up σ])) (ι u.[σ]) (map ι l..[σ])).
        ** now apply comp_mApp3.
        ** constructor.

  - constructor.
  - apply multistep_trans with (ι u.[σ] :: (map ι l)..[σ >>> ι]).
    + now apply comp_head.
    + apply multistep_trans with (ι u.[σ] :: (map ι l..[σ])).
      * now apply comp_tail.
      * constructor.
Qed.

Lemma ι_subst_rw u : (ι u).:ids = (u.:ids)>>>ι.
Proof. autosubst. Qed.

(* Resultados para a preservacao da substituicao por π *)
(* --------------------------------------------------- *)

Lemma π_ren_pres :
  (forall t ξ, π t.[ren ξ] = (π t).[ren ξ])
  /\
  (forall l ξ, map π l..[ren ξ] = (map π l)..[ren ξ]).
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; auto.
  - rewrite H. autosubst.
  - rewrite app_subst_comm. now f_equal.
  - f_equal ; try easy.
Qed.

Lemma π_up_subst σ : up (σ >>> π) = up σ >>> π.
Proof.
  f_ext.
  destruct x ; asimpl ; try easy.
  - rewrite (proj1 π_ren_pres). autosubst.
Qed.
  
Lemma π_subst_pres :
  (forall (t: LambdaM.term) σ, π t.[σ] = (π t).[σ >>> π])
  /\
  (forall (l: list LambdaM.term) σ, map π l..[σ] = (map π l)..[σ >>> π]).
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; f_equal ; try easy.
  - now rewrite π_up_subst.
  - rewrite app_subst_comm. now f_equal.
Qed.

Lemma π_subst_rw u : (π u).:ids = (u.:ids)>>>π.
Proof. autosubst. Qed.

(* Isomorfismo ao nível dos tipos! *)
(* ------------------------------- *)

Require Import SimpleTypes.

Lemma append_is_admissible Γ l l' A B C :
  Canonical.list_sequent Γ A l B ->
  Canonical.list_sequent Γ B l' C ->
  Canonical.list_sequent Γ A (l++l') C.
Proof.                  
  intros H1 H2.
  induction H1 ; asimpl ; auto.
Qed.  

Lemma app_is_admissible Γ t u l A B C :
  Canonical.sequent Γ t (Arr A B) ->
  Canonical.sequent Γ u A ->
  Canonical.list_sequent Γ B l C ->
  Canonical.sequent Γ t@(u,l) C.
Proof.
  destruct t ; intros ;
    inversion H ; subst ;
    econstructor ; eauto.
  - eapply append_is_admissible ; eauto.
  - eapply append_is_admissible ; eauto.
Qed.

Lemma π_is_admissible :
  forall Γ,
    (forall t A, LambdaM.sequent Γ t A -> Canonical.sequent Γ (π t) A)
    /\
    (forall A l B, LambdaM.list_sequent Γ A l B -> Canonical.list_sequent Γ A (map π l) B).
Proof.
  apply LambdaM.mut_sequent_ind ;
    intros ; asimpl ; auto.
  - eapply app_is_admissible ; eauto.
Qed.  

Lemma ι_is_admissible :
  forall Γ,
    (forall t A, Canonical.sequent Γ t A -> LambdaM.sequent Γ (ι t) A)
    /\
    (forall A l B, Canonical.list_sequent Γ A l B -> LambdaM.list_sequent Γ A (map ι l) B).
Proof.
  apply Canonical.mut_sequent_ind ;
    intros ; asimpl ; try econstructor ; eauto.
Qed.  
