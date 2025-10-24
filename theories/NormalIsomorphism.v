From Autosubst Require Import Autosubst.

Require Import Lambda Canonical LambdaIsomorphism.

From Coq Require Import List Relations.Relation_Definitions.
Import ListNotations.

Definition irreducible s := ~exists s', Lambda.step s s'.

(* In the text as claim 1. => *)
Proposition nfs_are_irreducible :
  (forall s, Lambda.normal s -> irreducible s)
  /\
  (forall s, apps s -> irreducible s).
Proof.
  apply Lambda.mut_normal_ind ; intros.
  - intro.
    apply H.
    destruct H0 as [s0 Hs0].
    inversion Hs0. now exists s'.
    - intro.
      apply H.
      destruct H0 as [s0 Hs0]. now exists s0.
    - intro. now destruct H.
    - intro.
      destruct H1 as [s0 Hs0].
      inversion Hs0 ; subst.
      + inversion a.
      + apply H. now exists s1'.
      + apply H0. now exists s2'.
Qed.

(* In the text as claim 1. <= *)
Proposition irreducible_is_nf s :
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

(* --- *)

Definition can_irreducible t := ~exists t', Canonical.step t t'.
Definition can_irreducible' l := ~exists l', Canonical.step' l l'.

(* In the text as Claim 3. *)
Proposition nts_are_irreducible :
  (forall t, Canonical.normal t -> can_irreducible t)
  /\
  (forall l, Canonical.normal_list l -> can_irreducible' l).
Proof.
  apply Canonical.mut_normal_ind ; intros.
  - intro H. destruct H as [u]. ainv.
  - intro H'. destruct H' as [u]. inversion H0 ; subst.
    + apply H. now exists t'.
    + ainv.
  - intro H'. destruct H' as [t']. inversion H1 ; subst.
    + apply H. now exists u'.
    + apply H0. now exists l'.
    + ainv.
  - intro H'. destruct H' as [l']. ainv.
  - intro H'. destruct H' as [l']. inversion H1 ; subst.
    + apply H. now exists u'.
    + apply H0. now exists l'0.
Qed.
  
Proposition irreducible_is_nt :
  (forall t, can_irreducible t -> Canonical.normal t)
  /\
  (forall l, can_irreducible' l -> Canonical.normal_list l).
Proof.
  apply Canonical.mut_term_ind ; intros.
  - constructor.
  - constructor. apply H.
    intro H'. destruct H' as [t'].
    apply Comp_Lamb in H1. eauto.
  - constructor.
    + apply H.
      intro H'. destruct H' as [u'].
      apply Comp_VariApp1 with (x:=x) (l:=l) in H2. eauto.
    + apply H0.
      intro H'. destruct H' as [l'].
      apply Comp_VariApp2 with (x:=x) (u:=u) in H2. eauto.
  - destruct H2. destruct l.
    + exists t.[u.:ids]. constructor. now left.
    + exists (t.[u.:ids]@(t0, l)). constructor. now right.
  - constructor.
  - constructor.
    + apply H. intro H'. destruct H' as [u'].
      apply H1. eauto.
    + apply H0. intro H'. destruct H' as [l'].
      apply H1. eauto.      
Qed.                      

(* --- *)

Corollary nf_inclusion s :
  Lambda.normal s -> Canonical.normal (ψ s).
Proof.
  intro H.
  apply nfs_are_irreducible in H.
  cut (can_irreducible (ψ s)).
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
