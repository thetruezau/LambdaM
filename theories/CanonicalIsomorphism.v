From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
Require Import MyRelations.

From Autosubst Require Import Autosubst.

Require Import LambdaM Canonical.
Require Import IsCanonical.

From Coq Require Import List.
Import ListNotations.

(* Injecção de λ⃗ em λm *)

Fixpoint i (t: Canonical.term) : LambdaM.term :=
  match t with
  | Vari x => Var x
  | Lamb t' => Lam (i t')
  | VariApp x u l => mApp (Var x) (i u) (map i l)
  | LambApp v u l => mApp (Lam (i v)) (i u) (map i l)
  end.

(* Projecção de λm em λ⃗ *)

Fixpoint p (t: LambdaM.term) : Canonical.term :=
  match t with
  | Var x => Vari x
  | Lam t' => Lamb (p t')
  | mApp v u l => (p v)@(p u, map p l)
  end.

(* Alguns lemas para auxiliar os resultados seguintes *)
(* -------------------------------------------------- *)

Lemma i_is_canonical :
  (forall t, is_canonical (i t))
  /\
  (forall l, is_canonical_list (map i l)).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ;
    now constructor.
Qed.

Lemma i_app_comm t u l :
  i t@(u,l) = capp (i t) (i u) (map i l).
Proof.
  destruct t ; asimpl ; f_equal ; apply map_app.
Qed.

(* p e i são bijecções *)
(* ------------------- *)

Theorem inversion1 :
  (forall (t: LambdaM.term), i (p t) = h t)
  /\
  (forall (l: list LambdaM.term), map i (map p l) = map h l).
Proof.
  apply LambdaM.mut_term_ind ;
    intros ; asimpl ; f_equal ; auto.
  - rewrite i_app_comm. now f_equal.
Qed.  

Corollary inversion1' :
  (forall (t: LambdaM.term), is_canonical t -> i (p t) = t)
  /\
  (forall (l: list LambdaM.term), is_canonical_list l -> map i (map p l) = l).
Proof.
  split.
  - intros t it.
    rewrite (proj1 h_is_surjective) ; try easy.
    apply inversion1.
  - intros l il.
    rewrite (proj2 h_is_surjective) ; try easy.
    apply inversion1.
Qed.

Proposition inversion2 :
  (forall (t: Canonical.term), p (i t) = t)
  /\
  (forall (l: list Canonical.term), map p (map i l) = l).
Proof.
  apply Canonical.mut_term_ind ;
    intros ; asimpl ; repeat f_equal ; auto.
Qed.

(* Resultados para a preservacao da substituicao por i *)
(* --------------------------------------------------- *)

Lemma i_ren_pres :
  (forall t ξ, i t.[ren ξ] = (i t).[ren ξ])
  /\
  (forall l ξ, map i l..[ren ξ] = (map i l)..[ren ξ]).
Proof.
  apply Canonical.mut_term_ind ; intros ; try easy.
  - asimpl. rewrite H. autosubst.
  - simpl. now f_equal.
  - simpl. f_equal ; try easy.
    + asimpl. rewrite H. autosubst.
  - asimpl. now f_equal.
Qed.

Lemma i_up_subst σ : up (σ >>> i) = up σ >>> i.
Proof.
  f_ext.
  destruct x ; asimpl ; try easy.
  - rewrite (proj1 i_ren_pres). autosubst.
Qed.

Theorem i_subst_pres :
  (forall t σ, i t.[σ] = h (i t).[σ >>> i])
  /\
  (forall l σ, map i l..[σ] = map h (map i l)..[σ >>> i]).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; try easy.
  - apply h_is_surjective. apply i_is_canonical.
  - rewrite i_up_subst. now f_equal.
  - rewrite i_app_comm. f_equal ; try easy.
    + apply h_is_surjective. apply i_is_canonical.
  - rewrite i_up_subst. now repeat f_equal.
  - now f_equal.  
Qed.

Lemma i_subst_rw u : (i u).:ids = (u.:ids)>>>i.
Proof. autosubst. Qed.

(* Resultados para a preservacao da substituicao por p *)
(* --------------------------------------------------- *)

Lemma p_ren_pres :
  (forall t ξ, p t.[ren ξ] = (p t).[ren ξ])
  /\
  (forall l ξ, map p l..[ren ξ] = (map p l)..[ren ξ]).
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; auto.
  - rewrite H. autosubst.
  - rewrite app_subst_comm. now f_equal.
  - f_equal ; try easy.
Qed.

Lemma p_up_subst σ : up (σ >>> p) = up σ >>> p.
Proof.
  f_ext.
  destruct x ; asimpl ; try easy.
  - rewrite (proj1 p_ren_pres). autosubst.
Qed.
  
Lemma p_subst_pres :
  (forall (t: LambdaM.term) σ, p t.[σ] = (p t).[σ >>> p])
  /\
  (forall (l: list LambdaM.term) σ, map p l..[σ] = (map p l)..[σ >>> p]).
Proof.
  apply LambdaM.mut_term_ind ; intros ; asimpl ; f_equal ; try easy.
  - now rewrite p_up_subst.
  - rewrite app_subst_comm. now f_equal.
Qed.

Lemma p_subst_rw u : (p u).:ids = (u.:ids)>>>p.
Proof. autosubst. Qed.

(* Isomorfismos ao nivel da reducao *)
(* -------------------------------- *)

Lemma step_can_is_compatible :
  Canonical.is_compatible
    (fun t t' => step_can (i t) (i t'))
    (fun l l' => step_can' (map i l) (map i l')).
Proof.
  split ; intros ; asimpl ; inversion H.
  - (* Caso λ.t -> λ.t' *)
    replace (Lam (h t0)) with (h (Lam t0)) ; try easy.
    replace (Lam (h t'0)) with (h (Lam t'0)) ; try easy.
    constructor. now constructor.
  - (* Caso x(u, l) -> x(u', l)*)
    specialize (proj2 i_is_canonical) with l. intro il.
    apply h_is_surjective in il. rewrite il.
    replace (mApp (Var x) (h t) (map h (map i l)))
      with (h (mApp (Var x) t (map i l))) ; try easy.
    replace (mApp (Var x) (h t') (map h (map i l)))
      with (h (mApp (Var x) t' (map i l))) ; try easy.
    constructor. now constructor.
  - (* Caso x(u, l) -> x(u, l')*)
    specialize (proj1 i_is_canonical) with u. intro iu.
    apply h_is_surjective in iu. rewrite iu.
    replace (mApp (Var x) (h (i u)) (map h l0))
      with (h (mApp (Var x) (i u) l0)) ; try easy.
    replace (mApp (Var x) (h (i u)) (map h l'0))
      with (h (mApp (Var x) (i u) l'0)) ; try easy.
    constructor. now constructor.
  - (* Caso (λ.t)(u, l) -> (λ.t')(u, l') *)
    specialize (proj1 i_is_canonical) with u. intro iu.
    apply h_is_surjective in iu. rewrite iu.
    specialize (proj2 i_is_canonical) with l. intro il.
    apply h_is_surjective in il. rewrite il.    
    replace (mApp (Lam (h t0)) (h (i u)) (map h (map i l)))
      with (h (mApp (Lam t0) (i u) (map i l))) ; try easy.
    replace (mApp (Lam (h t'0)) (h (i u)) (map h (map i l)))
      with (h (mApp (Lam t'0) (i u) (map i l))) ; try easy.
    (* here we use two compatibilty steps from system λm *)
    constructor. constructor. now constructor.
  - (* Caso (λ.t)(u, l) -> (λ.t)(u', l') *)
    specialize (proj1 i_is_canonical) with t. intro it.
    apply h_is_surjective in it. rewrite it.
    specialize (proj2 i_is_canonical) with l. intro il.
    apply h_is_surjective in il. rewrite il.    
    replace (mApp (Lam (h (i t))) (h t0) (map h (map i l)))
      with (h (mApp (Lam (i t)) t0 (map i l))) ; try easy.
    replace (mApp (Lam (h (i t))) (h t') (map h (map i l)))
      with (h (mApp (Lam (i t)) t' (map i l))) ; try easy.
    constructor. now constructor.
  - (* Caso (λ.t)(u, l) -> (λ.t')(u, l') *)
    specialize (proj1 i_is_canonical) with t. intro it.
    apply h_is_surjective in it. rewrite it.
    specialize (proj1 i_is_canonical) with u. intro iu.
    apply h_is_surjective in iu. rewrite iu.
    replace (mApp (Lam (h (i t))) (h (i u)) (map h l0))
      with (h (mApp (Lam (i t)) (i u) l0)) ; try easy.
    replace (mApp (Lam (h (i t))) (h (i u)) (map h l'0))
      with (h (mApp (Lam (i t)) (i u) l'0)) ; try easy.
    (* here we use two compatibilty steps from system λm *)
    constructor. now constructor.
  - specialize (proj2 i_is_canonical) with l. intro il.
    apply h_is_surjective in il. rewrite il.    
    replace (h t :: map h (map i l))
      with (map h (t :: map i l)) ; try easy.
    replace (h t' :: map h (map i l))
      with (map h (t' :: map i l)) ; try easy.
    constructor. now constructor.
  - specialize (proj1 i_is_canonical) with u. intro iu.
    apply h_is_surjective in iu. rewrite iu.    
    replace (h (i u) :: map h l0)
      with (map h ((i u) :: l0)) ; try easy.
    replace (h (i u) :: map h l'0)
      with (map h ((i u) :: l'0)) ; try easy.
    constructor. now constructor.
Qed.
    
Theorem i_step_pres :
  (forall (t t': Canonical.term),
      Canonical.step t t' -> step_can (i t) (i t'))
  /\
  (forall (l l': list Canonical.term),
      Canonical.step' l l' ->
      step_can' (map i l) (map i l')).
Proof.
  pose step_can_is_compatible as Hic. destruct Hic.
  apply Canonical.mut_comp_ind ; intros ; auto.
  - inversion b.
    + (* Caso Beta1 *)
      inversion H. subst. 
      specialize (proj1 i_is_canonical) with (LambApp t0 u []).
      intro ic1. apply h_is_surjective in ic1. rewrite ic1.
      rewrite (proj1 i_subst_pres).
      constructor. asimpl. 
      constructor. left. now constructor. 
    + (* Caso Beta2 *)
      inversion H. subst.
      specialize (proj1 i_is_canonical) with (LambApp t0 u (v::l)).
      intro ic1. apply h_is_surjective in ic1. rewrite ic1.
      rewrite i_app_comm.
      rewrite (proj1 i_subst_pres).
      rewrite capp_h_comm ; try apply i_is_canonical.
      constructor. asimpl.
      constructor. right. now constructor. 
Qed.

Theorem p_step_pres t t':
  step_can t t' -> Canonical.step (p t) (p t').
Proof.
  pose Canonical.step_is_compatible as Hic. destruct Hic.  

  intro Hs. induction Hs.
  rewrite<- (proj1 inversion1) with t.
  rewrite (proj1 inversion2).  
  rewrite<- (proj1 inversion1) with t'.
  rewrite (proj1 inversion2).

  induction H using LambdaM.sim_comp_ind
    with (P0 := fun l l' (_: step_β' l l')
                => step' (map p l) (map p l')) ;
    asimpl ; auto.
  - now apply step_comp_app1.
  - now apply step_comp_app2.
  - now apply step_comp_app3.

  - inversion b.
    + inversion H. subst. asimpl.
      constructor. left. constructor.
      rewrite p_subst_rw. apply p_subst_pres.
    + inversion H. subst. asimpl.
      constructor. right. constructor.
      f_equal. rewrite p_subst_rw. apply p_subst_pres.
Qed.

(* Isomorfismos admissiveis ao nivel das regras de tipificacao *)
(* ----------------------------------------------------------- *)

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

Lemma p_is_admissible :
  forall Γ,
    (forall t A, LambdaM.sequent Γ t A -> Canonical.sequent Γ (p t) A)
    /\
    (forall A l B, LambdaM.list_sequent Γ A l B -> Canonical.list_sequent Γ A (map p l) B).
Proof.
  apply LambdaM.mut_sequent_ind ;
    intros ; asimpl ; auto.
  - eapply app_is_admissible ; eauto.
Qed.  

Lemma i_is_admissible :
  forall Γ,
    (forall t A, Canonical.sequent Γ t A -> LambdaM.sequent Γ (i t) A)
    /\
    (forall A l B, Canonical.list_sequent Γ A l B -> LambdaM.list_sequent Γ A (map i l) B).
Proof.
  apply Canonical.mut_sequent_ind ;
    intros ; asimpl ; try econstructor ; eauto.
Qed.  
