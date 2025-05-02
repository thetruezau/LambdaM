Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* Sintaxe *)
(* ------- *)

Inductive λbar: Type :=
| VarApp (x: var) (l: list λbar)
| Lam (t: {bind λbar})
| TermApp (t: λbar) (l: list λbar).

Hint Constructors λbar : core.

Section simultaneous_induction_principle.
  Variable P : λbar -> Prop.

  Hypothesis HVarApp : forall x l, Forall P l -> P (VarApp x l).
  Hypothesis HLam : forall t, P t -> P (Lam t).
  Hypothesis HTermApp : forall t l, P t -> Forall P l ->
                             P (TermApp t l).

  Proposition sim_bar_ind : forall t, P t.
  Proof.
    fix rec 1. 
    assert (Hlist : forall l, Forall P l).
    { fix rec' 1. destruct l.
      - apply Forall_nil.
      - apply Forall_cons ; [ apply rec | apply rec' ]. }

    destruct t.
    - apply HVarApp.
      + apply Hlist.
    - apply HLam.
      + apply rec.
    - apply HTermApp.
      + apply rec.
      + apply Hlist.
  Qed.
End simultaneous_induction_principle.

(* Substituição *)
(* ------------ *)

Instance Ids_bar : Ids λbar.
Proof. intro x. exact (VarApp x []). Defined.
Instance Rename_bar : Rename λbar. derive. Defined.

Instance Subst_bar : Subst λbar. derive. Defined.
Instance SubstLemmas_bar : SubstLemmas λbar. derive. Defined.
