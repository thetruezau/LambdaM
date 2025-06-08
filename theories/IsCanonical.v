Require Import List.
Require Import LambdaM.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* ------------------------------- *)
(* predicado para termos canónicos *)

Inductive is_canonical: term -> Prop :=
| cVar (x: var) : is_canonical (Var x)
| cLam (t: {bind term}) : is_canonical t -> is_canonical (Lam t)                                                      
| cVarApp (x: var) (u: term) (l: list term) : is_canonical u -> is_canonical_list l -> is_canonical (mApp (Var x) u l)
| cLamApp (t: {bind term}) (u: term) (l: list term) : is_canonical t -> is_canonical u -> is_canonical_list l -> is_canonical (mApp (Lam t) u l)

with is_canonical_list: list term -> Prop :=
| cNil : is_canonical_list []
| cCons (u: term) (l: list term) : is_canonical u -> is_canonical_list l -> is_canonical_list (u::l).

Hint Constructors is_canonical is_canonical_list : core.

Scheme sim_is_canonical_ind := Induction for is_canonical Sort Prop
  with sim_is_canonical_list_ind := Induction for is_canonical_list Sort Prop.  

Definition app (v u: term) (l: list term) : term :=
  match v with
  | Var x => mApp v u l
  | Lam t => mApp v u l
  | mApp t u' l' => mApp t u' (l' ++ (u::l))
  end.

Lemma list_append_is_closed :
  forall l1 l2, is_canonical_list l1 -> is_canonical_list l2 -> is_canonical_list (l1++l2).
Proof.
  intros l1 l2 il1 il2.
  induction l1 ; simpl ; inversion il1 ; subst ; auto.
Qed.

Hint Resolve list_append_is_closed : core.

Lemma app_is_closed :
  forall t u l, is_canonical t -> is_canonical u -> is_canonical_list l ->
           is_canonical (app t u l).
Proof.
  intros t u l it iu il.
  destruct t as [x | t | v u' l'] ; asimpl ; try inversion it ; subst ; auto.
Qed.

Hint Resolve app_is_closed : core.
          
Instance Subst_Canonical : Subst term :=
  (fix inst (σ: var -> term) (s: term) : term :=
     match s with
     | Var x => σ x
     | Lam t => Lam (inst (up σ) t)
     | mApp v u l => app (inst σ v) (inst σ u) (mmap (inst σ) l)
   end).

Notation "s .{ σ }" := (Subst_Canonical σ s)                              
  (at level 2, σ at level 200, left associativity,
    format "s .{ σ }" ) : subst_scope.
                        
Notation "l ..{ σ }" := (mmap (Subst_Canonical σ) l)
  (at level 2, σ at level 200, left associativity,
    format "l ..{ σ }" ) : subst_scope.                             

Existing Instance Subst_term.

Definition is_canonical_subst (σ: var -> term) :=
  forall x, is_canonical (σ x).

Hint Unfold is_canonical_subst : core.

Lemma ren_is_closed :
  forall t, is_canonical t -> forall ξ, is_canonical (t.[ren ξ]).
Proof.
  induction 1 using sim_is_canonical_ind
    with (P0:=fun l _ => forall ξ, is_canonical_list (mmap (subst (ren ξ)) l)) ; intros ; asimpl ; auto.
Qed. 

Hint Resolve ren_is_closed : core.

Lemma up_subst_is_closed :
  forall σ, is_canonical_subst σ -> is_canonical_subst (up σ).
Proof.
  intros σ H. unfold is_canonical_subst.
  destruct x ; asimpl ; auto.
Qed.

Hint Resolve up_subst_is_closed : core.

Theorem subst_is_closed :
  forall t, is_canonical t -> forall σ, is_canonical_subst σ -> is_canonical t.{σ}.
Proof.
  intros t it.
  induction it using sim_is_canonical_ind
    with (P0:=fun l _ => forall σ, is_canonical_subst σ -> is_canonical_list l..{σ}) ; intros ; asimpl ; auto.
Qed.
          
(* Redução em termos canónicos *)
(* --------------------------- *)

Inductive β1' : relation term :=
| Can_Step_Beta1 (t: {bind term}) (u t': term):
  t' = t.{u .: ids} ->
  β1' (mApp (Lam t) u []) t'.

Inductive β2' : relation term :=
| Can_Step_Beta2 (t: {bind term}) (u u' t': term) (l: list term):
  t' = app t.{u .: ids} u' l ->
  β2' (mApp (Lam t) u (u'::l)) t'.

Definition step_can := comp (union _ β1' β2').
Definition step_can' := comp' (union _ β1' β2').
