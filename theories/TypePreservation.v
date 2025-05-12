Require Import List.
Require Import LambdaM.
Require Import Autosubst.Autosubst.

Import ListNotations.

(* Simple Types *)
(* ------------ *)

Inductive type: Type := Base | Arr : type -> type -> type.

(* Typing Rules *)
(* ------------ *)

Inductive sequent (Γ: var->type) : λm -> type -> Prop := 
| varAxiom (x: var) (A: type) :
  Γ x = A -> sequent Γ (Var x) A

| Right (t: λm) (A B: type) :
  sequent (A .: Γ) t B -> sequent Γ (Lam t) (Arr A B)

| mElim (t u: λm) (l: list λm) (A B C: type) :
  sequent Γ t (Arr A B) -> sequent Γ u A -> list_sequent Γ B l C ->
  sequent Γ (mApp t u l) C

with list_sequent (Γ:var->type) : type -> (list λm) -> type -> Prop :=
| nilAxiom (C: type) : list_sequent Γ C [] C

| Lft (u: λm) (l: list λm) (A B C:type) :
  sequent Γ u A -> list_sequent Γ B l C ->
  list_sequent Γ (Arr A B) (u :: l) C.

Hint Constructors sequent list_sequent : core.

Scheme sim_sequent_ind := Induction for sequent Sort Prop
  with sim_list_sequent_ind := Induction for list_sequent Sort Prop.

(* Subject Reduction *)
(* ----------------- *)

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

Check sim_comp_ind.

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
  - destruct x ; asimpl ; eauto.
Qed.

Lemma beta2_type_preservation :
  forall t t', β2 t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Admitted.

Lemma app_is_admissible :
  forall Γ l l' A B C,
    list_sequent Γ A l B -> list_sequent Γ B l' C ->
    list_sequent Γ A (l++l') C.
Proof.                  
  intros.
  induction H ; asimpl ; auto. (* simple induction! *)
Qed.
  
Lemma h_type_preservation :
  forall t t', LambdaM.H t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros.
  inversion H ; subst.
  inversion H0 ; subst. (* decompor mApp (mApp t0 u l) l' *)
  inversion H4 ; subst. (* decompor mApp t0 u l *)
  econstructor ; eauto.
  - eapply app_is_admissible ; eauto.
Qed.    
  
Definition list_type_preservation (l l': list λm) (_: step' l l') :=
  forall Γ A B, list_sequent Γ A l B -> list_sequent Γ A l' B.

Hint Unfold list_type_preservation : core.

Theorem type_preservation : 
  forall t t', step t t' -> forall Γ A, sequent Γ t A -> sequent Γ t' A.
Proof.
  intros t t' H.
  induction H using sim_comp_ind with (P0 := list_type_preservation) ; autounfold in * ; intros ;
    try (now inversion H ; econstructor ; eauto) ;
    try (now inversion H0 ; econstructor ; eauto).
    
  - inversion b.
    + inversion H0.
      * eapply beta1_type_preservation ; eassumption.
      * eapply beta2_type_preservation ; eassumption.
    + eapply h_type_preservation ; eassumption.
Qed.

Corollary type_preservation' Γ t A (_: sequent Γ t A) :
  forall t', step t t' -> sequent Γ t' A.
Proof.
  intros.
  eapply type_preservation ; eassumption.
Qed.
