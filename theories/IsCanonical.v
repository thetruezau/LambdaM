From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.
Require Import MyRelations.

From Autosubst Require Import Autosubst.
Require Import LambdaM.

From Coq Require Import List.
Import ListNotations.

(* ------------------------------- *)
(* predicado para termos canónicos *)

Inductive is_canonical: term -> Prop :=
| cVar (x: var) :
  is_canonical (Var x)

| cLam (t: {bind term}) :
  is_canonical t -> is_canonical (Lam t)

| cVarApp (x: var) (u: term) (l: list term) :
  is_canonical u -> is_canonical_list l ->
  is_canonical (mApp (Var x) u l)

| cLamApp (t: {bind term}) (u: term) (l: list term) :
  is_canonical t -> is_canonical u -> is_canonical_list l ->
  is_canonical (mApp (Lam t) u l)

with is_canonical_list: list term -> Prop :=
| cNil : is_canonical_list []

| cCons (u: term) (l: list term) :
  is_canonical u -> is_canonical_list l ->
  is_canonical_list (u::l).

Local Hint Constructors is_canonical is_canonical_list : core.

Scheme sim_is_canonical_ind := Induction for is_canonical Sort Prop
  with sim_is_canonical_list_ind := Induction for is_canonical_list Sort Prop.  

Combined Scheme mut_is_canonical_ind from sim_is_canonical_ind, sim_is_canonical_list_ind.

(* definition of h maximal reduction in in λm *)
(* ------------------------------------------ *)

Definition capp (v u: term) (l: list term) : term :=
  match v with
  | Var x        => mApp v u l
  | Lam t        => mApp v u l
  | mApp t u' l' => mApp t u' (l' ++ (u::l))
  end.

Fixpoint h (t: term) :=
  match t with
  | Var x      => Var x
  | Lam t      => Lam (h t)
  | mApp t u l => capp (h t) (h u) (map h l)
  end.

(* lets prove that the image of h is canonical *)
(* ------------------------------------------- *)

Lemma list_append_is_canonical l1 l2:
  is_canonical_list l1 -> is_canonical_list l2 ->
  is_canonical_list (l1++l2).
Proof.
  intros il1 il2.
  induction l1 ; simpl ; inversion il1 ; subst ; auto.
Qed.

Lemma capp_is_canonical t u l :
  is_canonical t -> is_canonical u -> is_canonical_list l ->
  is_canonical (capp t u l).
Proof.
  intros it iu il.
  destruct t as [x | t | v u' l'] ; asimpl ; auto.
  - inversion it ; subst. auto.
  - inversion it ; subst.
    + constructor ; try easy.
      * apply list_append_is_canonical ; auto.
    + constructor ; try easy.
      * apply list_append_is_canonical ; auto.
Qed.

Theorem h_is_canonical :
  (forall t, is_canonical (h t))
  /\
  (forall l, is_canonical_list (map h l)).
Proof.
  apply mut_term_ind ; intros ; asimpl ; auto.
  - apply capp_is_canonical ; auto.
Qed.

Theorem h_is_surjective :
  (forall t, is_canonical t -> t = h t)
  /\
  (forall l, is_canonical_list l -> l = map h l).
Proof.
  apply mut_is_canonical_ind ;
    intros ; asimpl ; repeat f_equal ; auto.
Qed.  

(* useful lemmas relating to map h *)
(* ------------------------------- *)

Lemma capp_h_comm t u l :
  is_canonical u ->
  is_canonical_list l ->
  capp (h t) u l = h (mApp t u l).
Proof.
  destruct t ; intros ; asimpl ; f_equal ;
    now apply h_is_surjective.
Qed.

Lemma capp_is_multistep_H t u l :
  multistep_H (mApp t u l) (capp t u l).
Proof.
  destruct t ; asimpl.
  - apply rt1n_refl.
  - apply rt1n_refl.
  - apply rt1n_trans with (mApp t1 t2 (l0 ++ u :: l)).
    + constructor. now constructor.
    + apply rt1n_refl.
Qed.

Lemma h_is_multistep_H :
  (forall t, multistep_H t (h t))
  /\
  (forall l, multistep_H' l (map h l)).
Proof.
  pose multistep_H_is_compatible as Hmic.

  apply mut_term_ind ; intros ; asimpl ; try constructor.
  - apply comp_lam with multistep_H' ; easy.
  - apply multistep_trans with (mApp (h t) u l).
    + apply comp_mApp1 with multistep_H' ; easy.
    + apply multistep_trans with (mApp (h t) (h u) l).
      * apply comp_mApp2 with multistep_H' ; easy.
      * apply multistep_trans with (mApp (h t) (h u) (map h l)).
        ** apply comp_mApp3 with multistep_H' ; easy.
        ** apply capp_is_multistep_H.
  - apply multistep_trans with (h u :: l).    
    + apply comp_head with multistep_H ; easy.
    + apply multistep_trans with (h u :: map h l).
      * apply comp_tail with multistep_H ; easy.
      * apply rt1n_refl.
Qed.

(* one step reduction in the canonical subsystem *)
(* --------------------------------------------- *)
  
Inductive canonical_relation (R: relation term): relation term :=
| Step_CanTerm t t' : R t t' ->
                      canonical_relation R (h t) (h t').

Inductive canonical_list_relation (R: relation (list term)): relation (list term) :=
| Step_CanList l l' : R l l' ->
                      canonical_list_relation R (map h l) (map h l').

Definition step_can := canonical_relation step_β.
Definition step_can' := canonical_list_relation step_β'.

(* typing system over the canonical system *)
(* --------------------------------------- *)

Require Import SimpleTypes.

Inductive canonical_sequent (Γ: var->type) : term -> type -> Prop :=
| Seq_CanTerm t A : sequent Γ t A -> canonical_sequent Γ (h t) A.

Inductive canonical_list_sequent (Γ: var->type) :
  type -> list term -> type -> Prop :=
| Seq_CanList l A B : list_sequent Γ A l B ->
                      canonical_list_sequent Γ A (map h l) B.
