From Coq Require Import List.
From Coq Require Import Relations.Relation_Definitions.

From Autosubst Require Import Autosubst.

(* --------------- *)
(* Auxiliary proof *)

Lemma mmap_append {A: Type} (f: A -> A) (l1 l2: list A) :
  mmap f (l1 ++ l2) = (mmap f l1) ++ (mmap f l2).
Proof.
  induction l1 ; asimpl ; try rewrite IHl1 ; auto.
Qed.

(* --- *)

Section LambdaM.
  Require Import LambdaM.
  
  Lemma step_subst :
    (forall s t, step s t -> forall σ, step s.[σ] t.[σ])
    /\
    (forall l l', step' l l' -> forall σ, step' l..[σ] l'..[σ]) .
  Proof.
    apply mut_comp_ind ; intros ; asimpl ;
      try (constructor ; apply H). 
    
    - destruct b as [Beta | H].
      + destruct Beta as [Beta1 | Beta2].
        * induction Beta1. subst.
          constructor. left. left. constructor. autosubst.
        * induction Beta2. subst.
          constructor. left. right. constructor. autosubst.
      + induction H. subst.
        constructor. right. constructor.
        now rewrite mmap_append.
  Qed.
End LambdaM.

Section Canonical.
  Require Import Canonical.
  
  Lemma step_subst_can :
  (forall s t, step s t -> forall σ, step s.[σ] t.[σ])
  /\
  (forall l l', step' l l' -> forall σ, step' l..[σ] l' ..[σ]).
  Proof.
    apply mut_comp_ind ; intros ; autounfold ; asimpl ;
      try (now constructor ; apply H).
    
    - apply step_comp_app2. apply H.
    - apply step_comp_app3. apply H.
    - destruct b as [Beta1 | Beta2] ; constructor.
      + induction Beta1. subst. left. constructor. autosubst.
      + induction Beta2. subst. right. asimpl. constructor.
        rewrite app_subst_comm. f_equal. autosubst.
  Qed.
End Canonical.

