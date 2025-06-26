From Coq Require Import List.
From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

Require Import Autosubst.Autosubst.
Require Import LambdaM.

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

(* definition of @ operation in λm *)
(* ------------------------------- *)

Definition app (v u: term) (l: list term) : term :=
  match v with
  | Var x        => mApp v u l
  | Lam t        => mApp v u l
  | mApp t u' l' => mApp t u' (l' ++ (u::l))
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

Lemma app_is_canonical t u l :
  is_canonical t -> is_canonical u -> is_canonical_list l ->
  is_canonical (app t u l).
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
  
(* app does H reduction *)
(* -------------------- *)

Theorem app_is_multistep_H t u l :
  multistep_H (mApp t u l) (app t u l).
Proof.
  destruct t ; asimpl ; try constructor.
  - apply rt1n_trans with (mApp t1 t2 (l0 ++ u :: l)).
    + now constructor.
    + now constructor.
Qed.
