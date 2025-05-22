Require Import List.
Require Import SimpleTypes Canonical.
Require Import Autosubst.Autosubst.

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

Definition list_type_renaming Γ A l B (_: list_sequent Γ A l B)
  := forall Δ ξ, Γ = (ξ >>> Δ) -> list_sequent Δ A l..[ren ξ] B.

Lemma type_renaming Γ t A (s: sequent Γ t A) :
  forall Δ ξ, Γ = (ξ >>> Δ) -> sequent Δ t.[ren ξ] A.
Proof.
  induction s using sim_sequent_ind
    with (P0 := list_type_renaming) ;
    intros ; subst ; asimpl ; econstructor ; eauto.
  - apply IHs. autosubst.
  - apply IHs1. autosubst.
Qed.      

Definition list_type_substitution Γ A l B (ls:list_sequent Γ A l B) :=
  forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> list_sequent Δ A l..[σ] B.

Lemma type_substitution Γ t A (s: sequent Γ t A) :
  forall σ Δ, (forall x, sequent Δ (σ x) (Γ x)) -> sequent Δ t.[σ] A.
Proof.  
  induction s using sim_sequent_ind
    with (P0 := list_type_substitution) ;
    intros ; asimpl ; subst ; try econstructor ; eauto.
  - apply IHs. destruct x ; asimpl ; auto.
    + eapply type_renaming ; eauto.
  - eapply app_is_admissible ; eauto.
    rewrite<- e. apply H.
  - apply IHs1. destruct x ; asimpl ; auto.
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
  
Definition list_type_preservation (l l': list λc) (_: step' l l') :=
  forall Γ A B, list_sequent Γ A l B -> list_sequent Γ A l' B.

Hint Unfold list_type_preservation : core.

Theorem type_preservation : 
  forall t t', step t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros t t' H.
  induction H using sim_comp_ind with (P0 := list_type_preservation) ;
    autounfold in * ; intros ;
    try (now inversion H ; econstructor ; eauto) ;
    try (now inversion H0 ; econstructor ; eauto).
    
  - inversion b.
    + eapply beta1_type_preservation ; eassumption.
    + eapply beta2_type_preservation ; eassumption.
Qed.

Corollary type_preservation' Γ t A (_: sequent Γ t A) :
  forall t', step t t' -> sequent Γ t' A.
Proof.
  intros.
  eapply type_preservation ; eassumption.
Qed.
