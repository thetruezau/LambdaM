Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.

(* The ordinary λ-calculus *)
(* ----------------------- *)

Inductive term: Type :=
| Var (x: var)
| Lam (t: {bind term})
| App (s t: term).

(* autosubst sorcery *)
(* ----------------- *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

(* beta reduction *)
(* -------------- *) 

Inductive step : relation term :=
| Step_Beta s s' t : s' = s.[t .: ids] ->
                     step (App (Lam s) t) s'
| Step_Abs (s s': {bind term}) : step s s' ->
                                 step (Lam s) (Lam s')
| Step_App1 s s' t: step s s' ->
                    step (App s t) (App s' t)
| Step_App2 s t t': step t t' ->
                    step (App s t) (App s t').

(* typing rules *)
(* ------------ *)

Require Import SimpleTypes.

Inductive sequent (Γ: var->type) : term -> type -> Prop := 
| Ax (x: var) (A: type) :
  Γ x = A ->
  sequent Γ (Var x) A

| Intro (t: term) (A B: type) :
  sequent (A .: Γ) t B ->
  sequent Γ (Lam t) (Arr A B)
                                 
| Elim (s t: term) (A B: type) :
  sequent Γ s (Arr A B) ->
  sequent Γ t A ->
  sequent Γ (App s t) B.
