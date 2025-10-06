From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
Require Import MyRelations.

From Autosubst Require Import Autosubst.

From Coq Require Import List.
Import ListNotations.

Require Import LambdaM IsCanonical.

(* Confluence of multistep_H in LambdaM *)
(* ------------------------------------ *)

Lemma capp_assoc t u l u' l' (it: is_canonical t):
  capp (capp t u l) u' l' = capp t u (l++u'::l').
Proof.
  destruct it ; simpl ; try reflexivity.
  - now rewrite<- app_assoc.
  - now rewrite<- app_assoc.
Qed.

Lemma step_H_collapse :
  (forall t t', step_H t t' -> h t = h t')
  /\
  (forall l l', step_H' l l' -> map h l = map h l').
Proof.
  apply mut_comp_ind ; intros ; simpl ; try now f_equal.
  - inversion b. subst. simpl. rewrite capp_assoc.
    + now rewrite map_app. 
    + apply h_is_canonical.
Qed.

Corollary multistep_H_collapse t t' :
  multistep_H t t' -> h t = h t'.
Proof.
  induction 1 as [u | u u1 u2].
  - reflexivity.
  - rewrite<- IHclos_refl_trans_1n. now apply step_H_collapse.
Qed.

Corollary H_confluence t t1 t2 :
  multistep_H t t1 -> multistep_H t t2 ->
  exists t', multistep_H t1 t' /\ multistep_H t2 t'. 
Proof.
  intros Ht1 Ht2. exists (h t). split.
  - apply multistep_H_collapse in Ht1. rewrite Ht1.
    apply h_is_multistep_H.
  - apply multistep_H_collapse in Ht2. rewrite Ht2.
    apply h_is_multistep_H.
Qed.

(* Given the confluence of the STLC, we may even prove
 confluence in the canonical subsystem and in LambdaM! *)
(* --------------------------------------------------- *)

Require Import Lambda LambdaIsomorphism
  CanonicalIsomorphism Conservativeness.

Section Confluence.
  Hypothesis Lambda_confluence : forall s s1 s2,
      Lambda.multistep s s1 -> Lambda.multistep s s2 ->
      exists s', Lambda.multistep s1 s' /\ Lambda.multistep s2 s'.

  Corollary Canonical_confluence : forall t t1 t2,
      Canonical.multistep t t1 -> Canonical.multistep t t2 ->
      exists t', Canonical.multistep t1 t' /\ Canonical.multistep t2 t'.
  Proof.
    intros t t1 t2 Htt1 Htt2.
    apply θ_multistep_pres in Htt1.
    apply θ_multistep_pres in Htt2.
    specialize (Lambda_confluence _ _ _ Htt1 Htt2) as (s & H1s & H2s).
    exists (ψ s). split.
    - apply ψ_multistep_pres in H1s.
      now rewrite (proj1 LambdaIsomorphism.inversion1) in H1s.
    - apply ψ_multistep_pres in H2s.
      now rewrite (proj1 LambdaIsomorphism.inversion1) in H2s.
  Qed.

  Corollary LambdaM_confluence : forall t t1 t2,
    LambdaM.multistep t t1 -> LambdaM.multistep t t2 ->
    exists t', LambdaM.multistep t1 t' /\ LambdaM.multistep t2 t'.
  Proof.
    intros t t1 t2 Htt1 Htt2.
    apply conservativeness2' in Htt1.
    apply conservativeness2' in Htt2.
    specialize (Canonical_confluence _ _ _ Htt1 Htt2) as (t' & H1 & H2).
    exists (i t'). split.
    - apply conservativeness in H1.
      rewrite (proj1 inversion1) in H1.
      apply multistep_trans with (h t1).
      + apply multistep_H_inclusion.
        apply h_is_multistep_H.
      + assumption.
    - apply conservativeness in H2.
      rewrite (proj1 inversion1) in H2.
      apply multistep_trans with (h t2).
      + apply multistep_H_inclusion.
        apply h_is_multistep_H.
      + assumption.
  Qed.
End Confluence.
