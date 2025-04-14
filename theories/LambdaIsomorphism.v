Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import Canonical.

Import ListNotations.

(* The usual λ-calculus *)
(* -------------------- *)

Inductive λ: Type :=
| Var (x: var)
| Lam (t: {bind λ})
| App (s t: λ).

Instance Ids_λ : Ids λ. derive. Defined.
Instance Rename_λ : Rename λ. derive. Defined.
Instance Subst_λ : Subst λ. derive. Defined.
Instance SubstLemmas_λ : SubstLemmas λ. derive. Defined.

Inductive step : relation λ :=
| Step_Beta s s' t : s' = s.[t .: ids] ->
                     step (App (Lam s) t) s'
| Step_Abs s s' : step s s' ->
                  step (Lam s) (Lam s')
| Step_App1 s s' t: step s s' ->
                    step (App s t) (App s' t)
| Step_App2 s t t': step t t' ->
                    step (App s t) (App s t').

(*   G:   λ --> λc    *)
(* ------------------ *)

Fixpoint g (s: λ) (l: list λc) : λc :=
  match s with
  | Var x => match l with
            | [] => Vari x
            | (u::l) => VariApp x u l
            end
  | Lam t => match l with
            | [] => Lamb (g t [])
            | (u::l) => LambApp (g t []) u l
            end
  | App s t => g s ((g t [])::l)
  end.

Definition G (s: λ) : λc := g s [].
Hint Unfold G : core.

(*   H:   λc --> λ    *)
(* ------------------ *)

Definition biApp (i: λc -> λ) (s1: λ) (s2: λc) : λ := App s1 (i s2).
Hint Unfold biApp : core.

Fixpoint H (s: λc) : λ :=
  match s with
  | Vari x => Var x
  | Lamb t => Lam (H t)
  | VariApp x u l => fold_left (biApp H) (u::l) (Var x)
  | LambApp t u l => fold_left (biApp H) (u::l) (Lam (H t))
  end.

Definition h (s: λ) (l: list λc) : λ := fold_left (biApp H) l s.
Hint Unfold h : core.
       
(* Lemas complementares sobre g e h *)
(* -------------------------------- *)

Lemma forall_implies_aux_inversion1 :
  forall l, Forall (fun u => G (H u) = u) l ->
       forall l' s, g (h s l) l' = g s (l++l').
Proof.
  intros l H. induction H as [| u l]; intros.
  - asimpl. f_equal.
  - asimpl in *. autounfold in IHForall. rewrite IHForall.
    autounfold. asimpl. f_equal. f_equal. assumption.
Qed.

Lemma aux_inversion2 :
  forall s l, H (g s l) = h s l.
Proof.
  induction s ; intros.
  - destruct l ; asimpl ; reflexivity.
  - destruct l ; asimpl ; repeat f_equal ; auto.
  - asimpl. rewrite IHs1. asimpl. autounfold.
    rewrite IHs2. asimpl. reflexivity.
Qed.

(* G e H são bijecções ao nível da sintaxe *)
(* --------------------------------------- *)

Theorem inversion1 : forall t, G (H t) = t.
Proof.
  induction t using sim_λc_ind.
  - reflexivity.
  - asimpl. f_equal. assumption.
  - asimpl. fold (h (biApp H (Var x) t) l).
    rewrite forall_implies_aux_inversion1 ; [| assumption].
    asimpl. f_equal ; [assumption | apply app_nil_r].
  - asimpl. fold (h (biApp H (Lam (H t1)) t2) l).
    rewrite forall_implies_aux_inversion1 ; [| assumption].
    asimpl. f_equal ; [| |apply app_nil_r] ; assumption.
Qed.

Theorem inversion2 : forall (s: λ), H (G s) = s.
Proof.
  induction s ; asimpl.
  - reflexivity.
  - autounfold in IHs. f_equal. assumption.
  - rewrite aux_inversion2. asimpl. autounfold. f_equal. apply IHs2.
Qed.

(* Alguns lemas para os resultados sobre substituição *)
(* -------------------------------------------------- *)

(*
Lemma fold_subst_pres (σ: var->λc) :
  forall l, Forall (fun u => H u.[σ] = (H u).[σ>>>H]) l ->
       forall s, fold_left (biApp H) l..[σ] s.[σ>>>H]
          = (fold_left (biApp H) l s).[σ>>>H].
Proof.
  intros l H0. induction H0 ; intro.
  - reflexivity.
  - asimpl. rewrite<- IHForall.
    autounfold. asimpl. repeat f_equal. assumption.
Qed.

Corollary fold_ren_pres ξ :
  forall l, Forall (fun u => H u.[ren ξ] = (H u).[ren ξ]) l ->
       forall s, fold_left (biApp H) l..[ren ξ] s.[ren ξ]
          = (fold_left (biApp H) l s).[ren ξ].
Proof.
  assert (ren ξ = ren ξ >>> H).
  - f_ext. simpl. reflexivity.
  - rewrite H0. apply fold_subst_pres.
Qed.

Lemma H_ren_pres :
  forall s ξ, H s.[ren ξ] = (H s).[ren ξ].
Proof.
  induction s using sim_λc_ind ; intros.
  - reflexivity.
  - asimpl. f_equal. apply IHs.
  - simpl. rewrite<- fold_ren_pres.
    + autounfold. asimpl. repeat f_equal. apply IHs.
    + induction H0 ; auto.
  - simpl. rewrite<- fold_ren_pres.
    + autounfold. asimpl. repeat f_equal.
      * apply IHs1.
      * apply IHs2.
    + induction H0 ; auto.
Qed.

Lemma H_subst_pres :
  forall s σ, H s.[σ] = (H s).[σ>>>H].
Proof.
  induction s using sim_λc_ind ; intros. 
  - reflexivity.
  - simpl. f_equal. rewrite IHs. f_equal.
    f_ext. destruct x ; asimpl ; [reflexivity | apply H_ren_pres].
  - simpl. destruct  (σ x) ; asimpl.
    + rewrite<- fold_subst_pres.
      * autounfold. repeat f_equal. asimpl. f_equal.
Qed.

*)

Lemma g_is_multiapp : (*talvez pudesse provar de maneira diferente!*)
  forall s u l, g s (u::l) = (G s)@(u, l).
Proof.
  intros. rewrite<- inversion2 at 1.
  destruct (G s) as [x | t | x u' l' | t u' l'] ; intros ; asimpl.
  - reflexivity.
  - fold (G (H t)). rewrite inversion1. reflexivity.
  - unfold biApp at 2. fold (h (App (Var x) (H u')) l').
    rewrite forall_implies_aux_inversion1.
    + asimpl. f_equal. apply inversion1.
    + induction l' ; constructor ; auto. apply inversion1.
  - unfold biApp at 2. fold (h (App (Lam (H t)) (H u')) l').
    rewrite forall_implies_aux_inversion1.
    + asimpl. f_equal ; apply inversion1.
    + induction l' ; constructor ; auto. apply inversion1.
Qed.

Lemma g_ren_pres :
  forall s l ξ, g s.[ren ξ] l..[ren ξ] = (g s l).[ren ξ].
Proof.
  induction s ; intros.
  - destruct l as [| u l] ; asimpl.
    + reflexivity.
    + apply g_is_multiapp.
  - destruct l as [| u l] ; asimpl ; f_equal.
    + specialize IHs with [] (upren ξ). asimpl in IHs. assumption.
    + specialize IHs with [] (upren ξ). asimpl in IHs. assumption.
  - asimpl. rewrite<- IHs1. asimpl. rewrite<- IHs2. asimpl. reflexivity.
Qed.

Lemma G_ren_pres :
  forall s ξ, G s.[ren ξ] = (G s).[ren ξ].
Proof.
  induction s ; intros ; asimpl.
  - reflexivity.
  - f_equal. apply IHs.
  - fold (G s2.[ren ξ]). fold (G s2). rewrite IHs2.
    specialize g_ren_pres with s1 [G s2] ξ. auto.
Qed.

Lemma up_sigma_G σ : up (σ >>> G) = up σ >>> G.
Proof.
  f_ext. destruct x ; asimpl.
  - reflexivity.
  - fold (G (σ x).[ren (+1)]). symmetry. apply G_ren_pres.
Qed.

Lemma up_sigma_H σ : up (σ >>> H) = up σ >>> H.
Proof.
  f_ext. destruct x ; asimpl.
  - reflexivity.
  - 
Admitted.

Lemma g_subst_pres :
  forall s l σ, g s.[σ] l..[σ >>> G] = (g s l).[σ >>> G].
Proof.
  induction s ; intros.
  - destruct l as [| u l] ; asimpl.
    + reflexivity.
    + apply g_is_multiapp.
  - destruct l as [| u l] ; asimpl.
    + f_equal. rewrite up_sigma_G.
      set (up σ) as σ'. specialize IHs with [] σ'.
      asimpl in IHs. assumption.
    + f_equal. rewrite up_sigma_G.
      set (up σ) as σ'. specialize IHs with [] σ'.
      asimpl in IHs. assumption.
  - asimpl. rewrite<- IHs1. asimpl. rewrite<- IHs2. asimpl. reflexivity.
Qed.

Lemma h_subst_pres :
  forall l s σ, h s.[σ >>> H] l..[σ] = (h s l).[σ >>> H].
Proof.
  induction l as [| u l]; intros ; asimpl.
  - reflexivity.
  - unfold biApp at 2 4.
    fold (h (App s.[σ >>> H] (H u.[σ])) l..[σ]).
    fold (h (App s (H u)) l). rewrite<- IHl. asimpl.
    repeat f_equal. 
Admitted.

(* As bijecções preservam a substituição *)
(* ------------------------------------- *)

Theorem G_subst_pres :
  forall s σ, G s.[σ] = (G s).[σ >>> G].
Proof.
  induction s ; intros ; asimpl.
  - reflexivity.
  - f_equal. rewrite up_sigma_G. apply IHs.
  - specialize g_subst_pres with s1 [G s2] σ. asimpl.
    fold (G s2). fold (G s2.[σ]). rewrite IHs2. auto. 
Qed.

Theorem H_subst_pres :
  forall s σ, H s.[σ] = (H s).[σ >>> H].
Proof.
  induction s using sim_λc_ind ; intros ; asimpl.
  - reflexivity.
  - f_equal. rewrite up_sigma_H. apply IHs.
  - unfold biApp at 2. fold (h (App (Var x) (H s)) l). admit.
  - unfold biApp at 2 4.
    fold (h (App (Lam (H s1.[up σ])) (H s2.[σ])) l..[σ]).
    fold (h (App (Lam (H s1)) (H s2)) l).

Qed.

(* As bijecções preservam a relação de um passo *)
(* -------------------------------------------- *)
