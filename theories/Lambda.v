Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.

(* The ordinary λ-calculus *)
(* ----------------------- *)

Inductive λ: Type :=
| Var (x: var)
| Lam (t: {bind λ})
| App (s t: λ).

(* autosubst sorcery *)
(* ----------------- *)

Instance Ids_λ : Ids λ. derive. Defined.
Instance Rename_λ : Rename λ. derive. Defined.
Instance Subst_λ : Subst λ. derive. Defined.
Instance SubstLemmas_λ : SubstLemmas λ. derive. Defined.

(* beta reduction *)
(* -------------- *) 

Inductive step : relation λ :=
| Step_Beta s s' t : s' = s.[t .: ids] ->
                     step (App (Lam s) t) s'
| Step_Abs s s' : step s s' ->
                  step (Lam s) (Lam s')
| Step_App1 s s' t: step s s' ->
                    step (App s t) (App s' t)
| Step_App2 s t t': step t t' ->
                    step (App s t) (App s t').

(* typing rules *)
(* ------------ *)

Require Import SimpleTypes.

Inductive sequent (Γ: var->type) : λ -> type -> Prop := 
| Ax (x: var) (A: type) :
  Γ x = A -> sequent Γ (Var x) A

| Intro (t: λ) (A B: type) :
  sequent (A .: Γ) t B -> sequent Γ (Lam t) (Arr A B)
                                 
| Elim (s t: λ) (A B: type) :
  sequent Γ s (Arr A B) -> sequent Γ t A -> sequent Γ (App s t) B.
