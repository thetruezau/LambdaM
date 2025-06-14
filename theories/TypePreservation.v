Require Import List.
Require Import SimpleTypes LambdaM.
Require Import Autosubst.Autosubst.

Import ListNotations.

(* Subst and Ren Lemmas *)
(* -------------------- *)

Definition list_type_renaming Γ A l B (_: list_sequent Γ A l B)
  := forall Δ ξ, Γ = (ξ >>> Δ) -> list_sequent Δ A l..[ren ξ] B.

Lemma type_renaming Γ t A (s: sequent Γ t A) :
  forall Δ ξ, Γ = (ξ >>> Δ) -> sequent Δ t.[ren ξ] A.
Proof.
  induction s using sim_sequent_ind
    with (P0 := list_type_renaming) ;
    intros ; subst ; econstructor ; eauto.
  - assert (rw : up (ren ξ) = ren (upren ξ)). { autosubst. }
    rewrite rw. apply IHs. autosubst.
Qed.      

Definition list_type_substitution Γ A l B (ls:list_sequent Γ A l B) :=
  forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> list_sequent Δ A l..[σ] B.

Lemma type_substitution Γ t A (s: sequent Γ t A) :
  forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> sequent Δ t.[σ] A.
Proof.  
  induction s using sim_sequent_ind
    with (P0 := list_type_substitution) ;
    intros ; subst ; try econstructor ; eauto.
  - apply IHs. destruct x ; asimpl.
    + constructor. trivial.
    + eapply type_renaming ; eauto.
Qed.        

(* Subject Reduction *)
(* ----------------- *)

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
  
Definition list_type_preservation (l l': list term) (_: step' l l') :=
  forall Γ A B, list_sequent Γ A l B -> list_sequent Γ A l' B.

Hint Unfold list_type_preservation : core.

(* type_preservation : forall t t', step t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A. *)

Theorem type_preservation t t' :
  step t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros H. 
  
  induction H using sim_comp_ind with (P0 := list_type_preservation) ;
    autounfold in * ; intros ;
    try (now inversion H ; econstructor ; eauto) ;
    try (now inversion H0 ; econstructor ; eauto).

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
