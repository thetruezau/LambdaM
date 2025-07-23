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
