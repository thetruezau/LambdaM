Require Import List.
Require Import SimpleTypes Canonical.
Require Import Autosubst.Autosubst.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* Append and @ admissability *)
(* -------------------------- *)

Lemma append_is_admissible Γ l l' A B C :
  list_sequent Γ A l B -> list_sequent Γ B l' C ->
  list_sequent Γ A (l++l') C.
Proof.                  
  intros H1 H2.
  induction H1 ; asimpl ; auto.
Qed.  

Lemma app_is_admissible Γ t u l A B C :
  sequent Γ t (Arr A B) -> sequent Γ u A -> list_sequent Γ B l C ->
  sequent Γ t@(u,l) C.
Proof.
  destruct t ; intros ;
    inversion H ; subst ;
    econstructor ; eauto.
  - eapply append_is_admissible ; eauto.
  - eapply append_is_admissible ; eauto.
Qed.
    
(* Subst and Ren Lemmas *)
(* -------------------- *)

Lemma type_renaming :
  forall Γ,
    (forall t A, sequent Γ t A ->
            forall Δ ξ, Γ = (ξ >>> Δ) -> sequent Δ t.[ren ξ] A)
    /\
    (forall A l B, list_sequent Γ A l B ->
              forall Δ ξ, Γ = (ξ >>> Δ) -> list_sequent Δ A l..[ren ξ] B).
Proof.
  apply mut_sequent_ind ; 
    intros ; subst ; asimpl ; econstructor ; eauto.
  - apply H. now autosubst.
  - apply H. now autosubst.
Qed.      

Lemma type_substitution :
  forall Γ, 
    (forall t A, sequent Γ t A ->
            forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> sequent Δ t.[σ] A)
    /\
    (forall A l B, list_sequent Γ A l B ->
               forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> list_sequent Δ A l..[σ] B).
Proof.  
  apply mut_sequent_ind ; 
    intros ; asimpl ; subst ; try econstructor ; eauto.
  - apply H. destruct x ; asimpl ; auto.
    + eapply type_renaming ; eauto.
  - eapply app_is_admissible ; eauto.
    rewrite<- e. apply H1.
  - apply H. destruct x ; asimpl ; auto.
    + eapply type_renaming ; eauto.
Qed.        

(* Subject Reduction *)
(* ----------------- *)

Lemma beta1_type_preservation :
  forall t t', β1 t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros.
  inversion H ; subst.
  inversion H0 ; subst. (* decompor: LambApp t0 u [] *)
  inversion H7 ; subst. (* unificar: tipos A = B usando [] *)
  eapply type_substitution.
  - eapply H4.
  - destruct x ; asimpl ; eauto.
Qed.

Lemma beta2_type_preservation :
  forall t t', β2 t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros.
  inversion H ; subst.
  inversion H0 ; subst. (* decompor: LambApp t0 u (v::l) *)
  inversion H7 ; subst. (* decompor: v::l *)
  inversion H9 ; subst. (* unificar: tipos A = B0 usando l *)
  - eapply app_is_admissible ; eauto.
    eapply type_substitution ; eauto.
    + destruct x ; asimpl ; eauto.
  - eapply app_is_admissible ; eauto.
    eapply type_substitution ; eauto.
    + destruct x ; asimpl ; eauto.
Qed.

Theorem type_preservation :
  (forall t t', step t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A)
  /\
  (forall l l', step' l l' -> forall Γ A B, list_sequent Γ A l B -> list_sequent Γ A l' B).
Proof.
  apply mut_comp_ind ; intros ;
    try (now inversion H ; econstructor ; eauto) ;
    try (now inversion H0 ; econstructor ; eauto).
    
  - inversion b.
    + eapply beta1_type_preservation ; eassumption.
    + eapply beta2_type_preservation ; eassumption.
Qed.
  
(* Subject Reduction as a corollary *)
(* -------------------------------- 

Require Import LambdaM CanonicalIsomorphism.
Require Import TypePreservation Conservativeness.

Corollary type_preservation' Γ t t' A :
  Canonical.sequent Γ t A /\ Canonical.step t t' -> Canonical.sequent Γ t' A.
Proof.
  intros. destruct H as [Ht Hs].
  rewrite<- (proj1 inversion2) with t'.
  apply h_type_preservation.
  apply type_preservation_multistep with (t:=i t).
  split.
  - now apply i_type_preservation.
  - now apply conservativeness1.
Qed.

*)
