Require Import List.
Require Import SimpleTypes LambdaM.
Require Import Autosubst.Autosubst.

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
  apply mut_sequent_ind ; 
    intros ; subst ; econstructor ; eauto.
  - assert (simple_rw : up (ren ξ) = ren (upren ξ)). { autosubst. }
    rewrite simple_rw. apply H. now autosubst.
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
    intros ; subst ; try econstructor ; eauto.
  - apply H. destruct x ; asimpl.
    + now constructor. 
    + eapply type_renaming ; eauto.
Qed.        

(*   Lemmas for base steps   *)
(* ------------------------- *)

Lemma beta1_type_preservation :
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

Lemma beta2_type_preservation :
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
  
Lemma h_type_preservation :
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
  apply mut_comp_ind ; intros ;
    try (now inversion H ; econstructor ; eauto) ;
    try (now inversion H0 ; econstructor ; eauto).
  (* with this tactics we automatically solve trivial goals! *)
  
  - inversion b.
    + inversion H0.
      * eapply beta1_type_preservation ; eassumption.
      * eapply beta2_type_preservation ; eassumption.
    + eapply h_type_preservation ; eassumption.
Qed.

Corollary type_preservation' Γ t t' A :
  sequent Γ t A /\ step t t' -> sequent Γ t' A.
Proof.
  intro H. destruct H as [H1 H2].
  eapply type_preservation ; eassumption.
Qed.
