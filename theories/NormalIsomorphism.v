From Autosubst Require Import Autosubst.

Require Import Lambda Canonical LambdaIsomorphism.

From Coq Require Import List Relations.Relation_Definitions.
Import ListNotations.

Definition irreducible s := ~exists s', Lambda.step s s'.

(* In the text as claim 1. => *)
Theorem nfs_are_irreducible :
  (forall s, Lambda.normal s -> irreducible s)
  /\
  (forall s, apps s -> irreducible s).
Proof.
  apply Lambda.mut_normal_ind ; intros.
  - intro.
    apply H.
    destruct H0 as [s0 Hs0].
    inversion Hs0.
    now exists s'.
    - intro.
      apply H.
      destruct H0 as [s0 Hs0].
      now exists s0.
    - intro.
      now destruct H.
    - intro.
      destruct H1 as [s0 Hs0].
      inversion Hs0 ; subst.
      + inversion a.
      + apply H. now exists s1'.
      + apply H0. now exists s2'.
Qed.

(* In the text as claim 1. <= *)
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
    + cut (irreducible s1).
      * intro is1.
        apply IHs1 in is1. inversion is1.
        ** cut False ; [contradiction |]. subst. apply H.
           exists (s.[s2/]). now constructor.
        ** assumption.
      * intro. apply H.
        inversion H0.
        eapply Step_App1 in H1. eauto.
    + apply IHs2. intro. apply H.
      inversion H0.
      apply Step_App2 with (s1:=s1) in H1. 
      now exists (App s1 x).
Qed.

(* In the text as Claim 4. *)
Definition irreducible' t := ~exists t', Canonical.step t t'.
Conjecture nts_are_irreducible : forall t, Canonical.normal t -> irreducible' t.
Conjecture irreducible_is_nt : forall t, irreducible' t -> Canonical.normal t.

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
