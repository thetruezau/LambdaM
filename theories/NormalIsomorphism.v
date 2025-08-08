From Autosubst Require Import Autosubst.

Require Import Lambda Canonical LambdaIsomorphism.

From Coq Require Import List Relations.Relation_Definitions.
Import ListNotations.

Theorem inversion1 :
  (forall t, Canonical.normal t -> ψ (θ t) = t)
  /\
  (forall l, Canonical.normal_list l -> forall s, ψ (θ' s l) = ψ' s l).
Proof.
  apply Canonical.mut_normal_ind ; intros ; asimpl ; try easy.
  - now f_equal. 
  - fold (θ' (App (Var x) (θ u)) l).
    fold (ψ (θ' (App (Var x) (θ u)) l)).
    rewrite H0. asimpl. now f_equal.
  - fold (θ' (App s (θ u)) l).
    fold (ψ (θ' (App s (θ u)) l)).
    rewrite H0. asimpl. now repeat f_equal.
Qed.

Theorem inversion2 :
  (forall s, Lambda.normal s -> θ (ψ s) = s)
  /\
  (forall a, Lambda.apps a -> forall l, θ (ψ' a l) = θ' a l).
Proof.
  apply Lambda.mut_normal_ind ; intros.
  - asimpl. now f_equal.
  - now apply H with (l:=[]).
  - destruct l ; now asimpl.
  - asimpl. fold (ψ t).
    rewrite H. asimpl.
    fold (θ' (App s (θ (ψ t))) l).
    now rewrite H0.
Qed.

(*        Digression:      *)
(* proof using isomorphism *)
(* ----------------------- *)

Definition irreducible s := ~exists t, Lambda.step s t.

Theorem nfs_are_irreducible :
  (forall s, Lambda.normal s -> irreducible s)
  /\
  (forall s, apps s -> irreducible s).
Proof.
  apply Lambda.mut_normal_ind ; intros.
  - intro.
    apply H.
    destruct H0 as [t Ht].
    inversion Ht.
    now exists s'.
    - intro.
      apply H.
      destruct H0 as [t Ht].
      now exists t.
    - intro.
      now destruct H.
    - intro.
      destruct H1 as [t0 Ht0].
      inversion Ht0 ; subst.
      + inversion a.
      + apply H. now exists s'.
      + apply H0. now exists t'.
Qed.

Theorem irreducible_is_nf s :
  irreducible s -> Lambda.normal s.
Proof.
  induction s ; intro H.
  - constructor. constructor.
  - constructor. apply IHs.
    intro. apply H.
    inversion H0.
    apply Step_Abs in H1.
    now exists (Lam x).
  - constructor. constructor.
    + assert (Hs1 : irreducible s1).
      { intro. apply H.
        inversion H0.
        eapply Step_App1 in H1. eauto. }
      apply IHs1 in Hs1. inversion Hs1.
      * cut False ; [contradiction |].
        subst. apply H.
        exists (s.[s2/]). now constructor.
      * assumption.
    + apply IHs2. intro. apply H.
      inversion H0.
      apply Step_App2 with (s:=s1) in H1. 
      now exists (App s1 x).
Qed.

Definition irreducible' t := ~exists t', Canonical.step t t'.

Conjecture nts_are_irreducible :
  forall t, Canonical.normal t -> irreducible' t.

Conjecture irreducible_is_nt :
  forall t, irreducible' t -> Canonical.normal t.

Corollary nf_inclusion s :
  Lambda.normal s -> Canonical.normal (ψ s).
Proof.
  intro H.
  apply nfs_are_irreducible in H.
  cut (irreducible' (ψ s)).
  - apply irreducible_is_nt.
  - intro. apply H.
    inversion H0. apply θ_step_pres in H1.
    rewrite LambdaIsomorphism.inversion2 in H1.
    now exists (θ x).
Qed.

Corollary nt_inclusion t :
  Canonical.normal t -> Lambda.normal (θ t).
Proof.
  intro H.
  apply nts_are_irreducible in H.
  cut (irreducible (θ t)).
  - apply irreducible_is_nf.
  - intro. apply H.
    inversion H0. apply ψ_step_pres in H1.
    rewrite (proj1 LambdaIsomorphism.inversion1) in H1.
    now exists (ψ x).
Qed.
