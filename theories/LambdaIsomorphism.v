Require Import List.
Require Import Autosubst.Autosubst.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import Canonical CanonicalIsomorphism.

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

(*   F:   λc --> λ    *)
(* ------------------ *)

Fixpoint F (t: λc) : λ :=
  match t with
  | Vari x => Var x
  | Lamb t => Lam (F t)
  | VariApp x u l => fold_left (fun s0 t0 => App s0 (F t0)) (u::l) (Var x)
  | LambApp t u l => fold_left (fun s0 t0 => App s0 (F t0)) (u::l) (Lam (F t))
  end.

Definition f (s: λ) (l: list λc) : λ := fold_left (fun s0 t0 => App s0 (F t0)) l s.
Hint Unfold f : core.
       
(* Lemas complementares sobre g e h *)
(* -------------------------------- *)

Lemma forall_implies_aux_inversion1 :
  forall l, Forall (fun u => G (F u) = u) l ->
       forall l' s, g (f s l) l' = g s (l++l').
Proof.
  intros l H. induction H as [| u l]; intros.
  - asimpl. f_equal.
  - asimpl in *. fold (f (App s (F u)) l). rewrite IHForall. 
    asimpl. f_equal. f_equal. assumption.
Qed.

Lemma aux_inversion2 :
  forall s l, F (g s l) = f s l.
Proof.
  induction s ; intros.
  - destruct l ; asimpl ; reflexivity.
  - destruct l ; asimpl ; repeat f_equal ; auto.
  - asimpl. rewrite IHs1. asimpl. rewrite IHs2. reflexivity.
Qed.

(* G e H são bijecções ao nível da sintaxe *)
(* --------------------------------------- *)

Theorem inversion1 : forall t, G (F t) = t.
Proof.
  induction t using sim_λc_ind.
  - reflexivity.
  - asimpl. f_equal. assumption.
  - asimpl. fold (f (App (Var x) (F t)) l).
    rewrite forall_implies_aux_inversion1 ; [| assumption].
    asimpl. f_equal ; [assumption | apply app_nil_r].
  - asimpl. fold (f (App (Lam (F t1)) (F t2)) l).
    rewrite forall_implies_aux_inversion1 ; [| assumption].
    asimpl. f_equal ; [| |apply app_nil_r] ; assumption.
Qed.

Theorem inversion2 : forall s, F (G s) = s.
Proof.
  induction s ; asimpl.
  - reflexivity.
  - autounfold in IHs. f_equal. assumption.
  - rewrite aux_inversion2. asimpl. f_equal. apply IHs2.
Qed.

(* Alguns lemas para os resultados sobre substituição *)
(* -------------------------------------------------- *)

Lemma g_is_multiapp : (*talvez pudesse provar de maneira diferente!*)
  forall s u l, g s (u::l) = (G s)@(u, l).
Proof.
  intros. rewrite<- inversion2 at 1.
  destruct (G s) as [x | t | x u' l' | t u' l'] ; intros ; asimpl.
  - reflexivity.
  - fold (G (F t)). rewrite inversion1. reflexivity.
  - fold (f (App (Var x) (F u')) l').
    rewrite forall_implies_aux_inversion1.
    + asimpl. f_equal. apply inversion1.
    + induction l' ; constructor ; auto. apply inversion1.
  - fold (f (App (Lam (F t)) (F u')) l').
    rewrite forall_implies_aux_inversion1.
    + asimpl. f_equal ; apply inversion1.
    + induction l' ; constructor ; auto. apply inversion1.
Qed.

Lemma f_app_lemma : forall l l' s, f s (l ++ l') = f (f s l) l'.
Proof.
  intros l l'. induction l ; intros ; auto ; try apply IHl.
Qed.    
  
Lemma f_is_multiapp :
  forall t u l, F t@(u, l) = f (App (F t) (F u)) l.
Proof.
  destruct t as [x | t | x u' l' | t u' l'] ; intros ; asimpl ; auto.
  - fold (f (App (Var x) (F u')) (l' ++ u::l)).
    fold (f (App (Var x) (F u')) l').
    apply f_app_lemma. 
  - fold (f (App (Lam (F t)) (F u')) (l' ++ u::l)).
    fold (f (App (Lam (F t)) (F u')) l').
    apply f_app_lemma. 
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

Lemma forall_implies_f_subst_pres :
  forall l σ, Forall (fun u => F u.[σ] = (F u).[σ >>> F]) l ->
        forall s, f s.[σ >>> F] l..[σ] = (f s l).[σ >>> F].
Proof.
  intros l σ H. induction H as [| u l]; intros ; asimpl.
  - reflexivity.
  - fold (f (App s.[σ >>> F] (F u.[σ])) l..[σ]).
    fold (f (App s (F u)) l). rewrite<- IHForall. asimpl.
    repeat f_equal. apply H.
Qed.

Lemma F_ren_comp :
  forall ξ, ren ξ = ren ξ >>> F.
Proof. reflexivity. Qed.
  
(* isomorfismos preservam renamings *)

Lemma G_ren_pres :
  forall s ξ, G s.[ren ξ] = (G s).[ren ξ].
Proof.
  induction s ; intros ; asimpl.
  - reflexivity.
  - f_equal. apply IHs.
  - fold (G s2.[ren ξ]). fold (G s2). rewrite IHs2.
    specialize g_ren_pres with s1 [G s2] ξ. auto.
Qed.

Lemma F_ren_pres :
  forall s ξ, F s.[ren ξ] = (F s).[ren ξ].
Proof.
  induction s using sim_λc_ind ; intros ; asimpl.
  - reflexivity.
  - f_equal. apply IHs.
  - fold (f (App (Var x) (F s)) l). simpl.
    fold (f (App (Var (ξ x)) (F s.[ren ξ])) l..[ren ξ]).

    assert (app_rw : App (Var (ξ x)) (F s.[ren ξ]) = (App (Var x) (F s)).[ren ξ]).
    { asimpl. f_equal. apply IHs. }

    rewrite app_rw. rewrite F_ren_comp at 1 2.
    + apply forall_implies_f_subst_pres.
      induction H as [| u l] ; auto.
      
  - fold (f (App (Lam (F s1.[ren (upren ξ)])) (F s2.[ren ξ])) l..[ren ξ]).
    fold (f (App (Lam (F s1)) (F s2)) l).

    assert (app_rw : App (Lam (F s1.[ren (upren ξ)])) (F s2.[ren ξ]) = (App (Lam (F s1)) (F s2)).[ren ξ]).
    { asimpl. repeat f_equal ; [apply IHs1 | apply IHs2]. }

    rewrite app_rw. rewrite F_ren_comp at 1 2.
    + apply forall_implies_f_subst_pres.
      induction H as [| u l] ; auto.    
Qed.

Lemma up_sigma_G σ : up (σ >>> G) = up σ >>> G.
Proof.
  f_ext. destruct x ; asimpl.
  - reflexivity.
  - fold (G (σ x).[ren (+1)]). symmetry. apply G_ren_pres.
Qed.

Lemma up_sigma_F σ : up (σ >>> F) = up σ >>> F.
Proof.
  f_ext. destruct x ; asimpl.
  - reflexivity.
  - symmetry. apply F_ren_pres.
Qed.

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

Theorem F_subst_pres :
  forall s σ, F s.[σ] = (F s).[σ >>> F].
Proof.
  induction s using sim_λc_ind ; intros ; asimpl.
  - reflexivity.
  - f_equal. rewrite up_sigma_F. apply IHs.
  - fold (f (App (Var x) (F s)) l).
    rewrite<- forall_implies_f_subst_pres.
    + asimpl. rewrite<- IHs. apply f_is_multiapp.
    + induction H ; auto.
      
  - fold (f (App (Lam (F s1.[up σ])) (F s2.[σ])) l..[σ]).
    fold (f (App (Lam (F s1)) (F s2)) l).

    assert (rw_subst : (App (Lam (F s1)) (F s2)).[σ >>> F]
                       = App (Lam (F s1.[up σ])) (F s2.[σ])).
    { asimpl. f_equal.
      - f_equal. rewrite IHs1. f_equal. apply up_sigma_F.
      - rewrite IHs2. reflexivity. }

    rewrite<- rw_subst. apply forall_implies_f_subst_pres.
    + induction H ; auto.
Qed.

(* As bijecções preservam a relação de um passo *)
(* -------------------------------------------- *)
  
Lemma g_step_pres :
  forall s s', step s s' ->
          forall l, Canonical.step (g s l) (g s' l).
Proof.
  intros s s' H0. induction H0 ; intros ; subst.
  - asimpl.
    assert (g_subst : g s.[t/] [] = (g s []).[g t []/]).
    { fold (G s.[t/]). fold (G s). fold (G t). rewrite G_subst_pres.
      f_equal. f_ext. destruct x ; auto. }
    
    destruct l as [| u l].
    + constructor. left. constructor. exact g_subst.
    + constructor. right. constructor.
      rewrite<- g_subst. fold (G s.[t/]). apply g_is_multiapp.
  - destruct l as [| u l] ; asimpl.
    + constructor. apply IHstep.
    + constructor. apply IHstep.
  - asimpl. apply IHstep.
  - asimpl. repeat rewrite g_is_multiapp. apply step_comp_app2. apply IHstep.
Qed.
    
Corollary G_step_pres :
  forall (s s': λ), step s s' -> Canonical.step (G s) (G s').
Proof. intros s s' H0. apply g_step_pres. assumption. Qed.
  
Lemma f_step_pres :
  forall l (s s': λ), step s s' -> step (f s l) (f s' l).
Proof.
  induction l ; asimpl ; intros.
  - trivial.
  - fold (f (App s (F a)) l). fold (f (App s' (F a)) l).
    apply IHl. constructor. assumption.
Qed.

Theorem F_step_pres :
  forall (t t': λc), Canonical.step t t' -> step (F t) (F t').
Proof.
  assert (F_subst : forall s t, F s.[t/] = (F s).[F t/]).
  { intros s t. rewrite F_subst_pres.
    f_equal. f_ext. destruct x ; auto. }
  
  intros t t' H0. induction H0 using sim_comp_ind
    with (P0 := fun l l' (_: step' l l') =>
                  forall t, step (f t l) (f t l')) ;
    intros ; asimpl.
  - constructor. assumption.
  - apply f_step_pres. constructor. assumption.
  - apply IHcomp.
  - apply f_step_pres. apply Step_App1. constructor. assumption.
  - apply f_step_pres. apply Step_App2. assumption.
  - apply IHcomp.
  - inversion b as [Beta1 | Beta2].
    + inversion Beta1 ; subst ; asimpl.
      constructor. apply F_subst.      
    + inversion Beta2 ; subst. rewrite f_is_multiapp. asimpl.
      apply f_step_pres. constructor. constructor. apply F_subst.
  - apply f_step_pres. constructor. assumption.
  - apply IHcomp.
Qed.
