From Coq Require Import Relations.Relation_Definitions.

From Autosubst Require Import Autosubst.

(* The ordinary λ-calculus *)
(* ----------------------- *)

Inductive term: Type :=
| Var (x: var)
| Lam (s: {bind term})
| App (s1 s2: term).

(* Autosubst classes *)
(* ----------------- *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

(* Beta reduction *)
(* -------------- *) 

Inductive step : relation term :=
| Step_Beta (s: {bind term}) (s' u: term) :
  s' = s.[u .: ids] -> step (App (Lam s) u) s'
| Step_Abs s s' :
  step s s' -> step (Lam s) (Lam s')
| Step_App1 s1 s1' s2 :
  step s1 s1' -> step (App s1 s2) (App s1' s2)
| Step_App2 s1 s2 s2':
  step s2 s2' -> step (App s1 s2) (App s1 s2').

(* λ-terms in β-normal form *) 
(* ------------------------ *) 

Inductive normal: term -> Prop :=
| nLam s : normal s -> normal (Lam s)
| nApps s : apps s -> normal s
  
with apps: term -> Prop :=
| nVar x : apps (Var x)
| nApp s1 s2: apps s1 -> normal s2 -> apps (App s1 s2).

Scheme sim_normal_ind := Induction for normal Sort Prop
  with sim_apps_ind := Induction for apps Sort Prop.  

Combined Scheme mut_normal_ind from sim_normal_ind, sim_apps_ind.

(* Typing rules *)
(* ------------ *)

Require Import SimpleTypes.

Inductive sequent (Γ: var->type) : term -> type -> Prop := 
| Ax (x: var) (A: type) :
  Γ x = A ->
  sequent Γ (Var x) A

| Intro (s: term) (A B: type) :
  sequent (A .: Γ) s B ->
  sequent Γ (Lam s) (Arr A B)
                                 
| Elim (s1 s2: term) (A B: type) :
  sequent Γ s1 (Arr A B) ->
  sequent Γ s2 A ->
  sequent Γ (App s1 s2) B.
