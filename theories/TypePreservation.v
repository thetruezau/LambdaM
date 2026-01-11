Require Import SimpleTypes LambdaM.

From Autosubst Require Import Autosubst.

From Coq Require Import List.
Import ListNotations.

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
  apply mut_sequent_ind ; intros ; subst ; econstructor ; eauto.
  - rewrite up_upren_internal.
    + apply H. autosubst.
    + intros xi x. now asimpl. 
Qed.      

Lemma type_substitution :
  forall Γ, 
    (forall t A, sequent Γ t A ->
            forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> sequent Δ t.[σ] A)
    /\
    (forall A l B, list_sequent Γ A l B ->
               forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> list_sequent Δ A l..[σ] B).
Proof.  
  apply mut_sequent_ind ; intros ; subst ; try econstructor ; eauto.
  - apply H. destruct x ; asimpl.
    + now constructor. 
    + eapply type_renaming ; eauto.
Qed.

(*   Lemmas for base steps   *)
(* ------------------------- *)

Lemma beta1_is_admissible :
  forall t t', β1 t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros.
  inversion H ; subst.
  inversion H0 ; subst. (* decompor: mApp (Lam t0) u [] *)
  inversion H4 ; subst. (* decompor: Lam t0 *)
  inversion H7 ; subst. (* unificar: tipos A = B usando [] *)
  eapply type_substitution.
  - eapply H3.
  - destruct x ; asimpl ; auto.
Qed.

Lemma beta2_is_admissible :
  forall t t', β2 t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros.
  inversion H ; subst.
  inversion H0 ; subst. (* decompor: mApp (Lam t0) u (v::l) *)
  inversion H4 ; subst. (* decompor: Lam t0 *)
  inversion H7 ; subst. (* decompor: v::l *)
  inversion H10 ; subst. (* unificar: tipos A = B0 usando l *)
  - econstructor ; eauto.
    eapply type_substitution.
    + eapply H3.
    + destruct x ; asimpl ; eauto.
  - econstructor ; eauto.
    eapply type_substitution.
    + eapply H3.
    + destruct x ; asimpl ; eauto.
Qed.

Lemma append_is_admissible Γ l l' A B C :
  list_sequent Γ A l B -> list_sequent Γ B l' C ->
  list_sequent Γ A (l++l') C.
Proof.                  
  intros H1 H2.
  induction H1 ; asimpl ; auto.
Qed.
  
Lemma H_is_admissible :
  forall t t', LambdaM.H t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros.
  inversion H ; subst.
  inversion H0 ; subst. (* decompor mApp (mApp t0 u l) l' *)
  inversion H4 ; subst. (* decompor mApp t0 u l *)
  econstructor ; eauto.
  - eapply append_is_admissible ; eauto.
Qed.    

(* Subject Reduction for λm *)
(* ------------------------ *)

Theorem type_preservation :
  (forall t t', step t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A)
  /\
  (forall l l', step' l l' -> forall Γ A B, list_sequent Γ A l B -> list_sequent Γ A l' B).
Proof.
  apply mut_comp_ind ; intros ; try (now ainv ; eauto).
  (* with this tactic we automatically solve trivial goals! *)
  
  - inversion b.
    + inversion H0.
      * eapply beta1_is_admissible ; eassumption.
      * eapply beta2_is_admissible ; eassumption.
    + eapply H_is_admissible ; eassumption.
Qed.

Corollary type_preservation_multistep Γ t t' A:
  LambdaM.sequent Γ t A ->
  LambdaM.multistep t t' ->  
  LambdaM.sequent Γ t' A.
Proof.
  intros H1 H2. 
  induction H2 ; subst ; try easy.
  apply IHclos_refl_trans_1n.
  apply (proj1 type_preservation) with x ; try easy.
Qed.

(* As a corollary we get subject reduction *)
(*       for the canonical subsystem       *)
(* --------------------------------------- *)

Require Import Canonical CanonicalIsomorphism IsCanonical.
Require Import Conservativeness.

Corollary type_preservation' Γ t t' A :
  Canonical.sequent Γ t A ->
  Canonical.step t t' ->
  Canonical.sequent Γ t' A.
Proof.
  specialize (proj1 i_is_canonical) with t'. intro it'.
  apply h_fixpoints in it'.

  intros H1 H2.
  rewrite<- (proj1 inversion2) with t'.
  apply p_is_admissible. rewrite it'. constructor.
  apply type_preservation_multistep with (t:=i t).
  - apply i_is_admissible in H1. induction H1.
    apply type_preservation_multistep with (t:=t0).
    + assumption.
    + apply multistep_H_inclusion.
      apply h_is_multistep_H.
  - now apply conservativeness1.
Qed.

(*  And also for the STLC  *)
(* ----------------------- *)

Require Import Lambda LambdaIsomorphism.

Corollary type_preservation'' Γ t t' A :
  Lambda.sequent Γ t A ->
  Lambda.step t t' ->
  Lambda.sequent Γ t' A.
Proof.
  intros Hseq Hstep.
  rewrite<- LambdaIsomorphism.inversion2 with t'.
  apply θ_is_admissible.
  apply type_preservation' with (t:=ψ t).
  - now apply ψ_is_admissible.
  - now apply ψ_step_pres.
Qed.
