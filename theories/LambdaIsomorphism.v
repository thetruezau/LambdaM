From Coq Require Import Relations.Relation_Definitions.

From Autosubst Require Import Autosubst.

Require Import Lambda Canonical.

From Coq Require Import List.
Import ListNotations.

(*   θ:   λ⃗ --> λ    *)
(* ------------------ *)

Fixpoint θ (t: Canonical.term) : Lambda.term :=
  match t with
  | Vari x => Var x
  | Lamb t => Lam (θ t)
  | VariApp x u l => fold_left (fun s0 t0 => App s0 (θ t0)) (u::l) (Var x)
  | LambApp t u l => fold_left (fun s0 t0 => App s0 (θ t0)) (u::l) (Lam (θ t))
  end.

Definition θ' (s: Lambda.term) (l: list Canonical.term) : Lambda.term := fold_left (fun s0 t0 => App s0 (θ t0)) l s.
Hint Unfold θ' : core.

(*   ψ:   λ --> λ⃗    *)
(* ------------------ *)

Fixpoint ψ' (s: Lambda.term) (l: list Canonical.term) : Canonical.term :=
  match s with
  | Var x => match l with
            | [] => Vari x
            | (u::l) => VariApp x u l
            end
  | Lam t => match l with
            | [] => Lamb (ψ' t [])
            | (u::l) => LambApp (ψ' t []) u l
            end
  | App s t => ψ' s ((ψ' t [])::l)
  end.

Definition ψ (s: Lambda.term) : Canonical.term := ψ' s [].
Hint Unfold ψ : core.

(* θ e ψ são bijecções ao nível da sintaxe *)
(* --------------------------------------- *)

Theorem inversion1 :
  (forall (t: Canonical.term), ψ (θ t) = t)
  /\
  (forall (l: list Canonical.term) s, ψ (θ' s l) = ψ' s l).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; try easy.
  - now f_equal. 
  - fold (θ' (App (Var x) (θ u)) l).
    fold (ψ (θ' (App (Var x) (θ u)) l)).
    rewrite H0. asimpl. now f_equal.
  - fold (θ' (App (Lam (θ t)) (θ u)) l).
    fold (ψ (θ' (App (Lam (θ t)) (θ u)) l)).
    rewrite H1. asimpl. now f_equal.
  - fold (θ' (App s (θ u)) l).
    fold (ψ (θ' (App s (θ u)) l)).
    rewrite H0. asimpl. now repeat f_equal.
Qed.

Lemma aux_inversion2 :
  forall s l, θ (ψ' s l) = θ' s l.
Proof.
  induction s ; intros.
  - destruct l ; now asimpl.
  - destruct l ; asimpl ; repeat f_equal ; auto.
  - asimpl. rewrite IHs1. asimpl. now rewrite IHs2. 
Qed.

Theorem inversion2 : forall s, θ (ψ s) = s.
Proof.
  induction s ; asimpl ; try easy.
  - autounfold in IHs. now f_equal.
  - rewrite aux_inversion2. asimpl. now f_equal.
Qed.

(* Lemas para preservaçao de renamings *)
(* ----------------------------------- *)

Lemma θ_app_lemma :
  (forall v u l, θ v@(u,l) = θ' (App (θ v) (θ u)) l)
  /\
  (forall l s u' l', θ' s (l++(u'::l')) = θ' (App (θ' s l) (θ u')) l').
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; try easy.
  - fold (θ' (App (Var x) (θ u)) (l ++ u0 :: l0)).
    fold (θ' (App (Var x) (θ u)) l).
    now rewrite H0.
  - fold (θ' (App (Lam (θ t)) (θ u)) (l ++ u0 :: l0)).
    fold (θ' (App (Lam (θ t)) (θ u)) l).
    now rewrite H1.
  - fold (θ' (App s (θ u)) (l ++ u' :: l')).
    fold (θ' (App s (θ u)) l).
    now rewrite H0.
Qed.

Lemma head_as_append (A: Type) (x:A) (xs: list A) : [x]++xs = x::xs.
Proof. easy. Qed.

Corollary ψ_app_lemma : forall s u l, ψ' s (u :: l) = (ψ s)@(u, l).
Proof.
  intros s u l.
  destruct s ; asimpl ; try easy.
  - rewrite<- (proj2 inversion1).
    rewrite<- head_as_append.
    rewrite (proj2 θ_app_lemma). 
    rewrite<- aux_inversion2 with (s:=s1).
    rewrite<- (proj1 θ_app_lemma). 
    now rewrite (proj1 inversion1).
Qed.    
  
Lemma θ_ren_pres :
  (forall t ξ, θ t.[ren ξ] = (θ t).[ren ξ])
  /\
  (forall l s ξ, θ' s.[ren ξ] l..[ren ξ] = (θ' s l).[ren ξ]).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; try easy.
  - now f_equal.
  - fold (θ' (App (Var x) (θ u)) l).
    rewrite<- H0.
    rewrite (proj1 θ_app_lemma).
    now rewrite H.
  - fold (θ' (App (Lam (θ t.[ren (upren ξ)])) (θ u.[ren ξ])) l..[ren ξ]).
    fold (θ' (App (Lam (θ t)) (θ u)) l).
    rewrite H, H0.
    rewrite<- H1.
    now asimpl.
  - fold (θ' (App s.[ren ξ] (θ u.[ren ξ])) l..[ren ξ]).
    fold (θ' (App s (θ u)) l).
    rewrite H.
    rewrite<- H0.
    now asimpl.
Qed.

Lemma ψ_ren_pres :
  (forall s l ξ, ψ' s.[ren ξ] l..[ren ξ] = (ψ' s l).[ren ξ]).
Proof.
  induction s ; intros.
  - destruct l as [| u l] ; asimpl ; try easy.
  - destruct l as [| u l] ; asimpl ; try easy.
    + now rewrite<- IHs.
    + now rewrite<- IHs.   
  - asimpl. rewrite<- IHs1. asimpl. now rewrite<- IHs2.
Qed.
    
(* Lemas para preservaçao de substituição *)
(* -------------------------------------- *)

Lemma θ_up_subst σ : up (σ >>> θ) = up σ >>> θ.
Proof.
  f_ext. destruct x ; asimpl ; try easy.
  - now rewrite (proj1 θ_ren_pres).
Qed.

Lemma θ_subst_pres :
  (forall t σ, θ t.[σ] = (θ t).[σ >>> θ])
  /\
  (forall l s σ, θ' s.[σ >>> θ] l..[σ] = (θ' s l).[σ >>> θ]).
Proof.
  apply Canonical.mut_term_ind ; intros ; asimpl ; try easy.
  - f_equal. now rewrite θ_up_subst.
  - fold (θ' (App (Var x) (θ u)) l).
    rewrite<- H0.
    rewrite (proj1 θ_app_lemma).
    now rewrite H.
  - fold (θ' (App (Lam (θ t.[up σ])) (θ u.[σ])) l..[σ]).
    fold (θ' (App (Lam (θ t)) (θ u)) l).
    rewrite H, H0.
    rewrite<- θ_up_subst.
    rewrite<- H1.
    now asimpl.
  - fold (θ' (App s.[σ >>> θ] (θ u.[σ])) l..[σ]).
    fold (θ' (App s (θ u)) l).
    rewrite H.
    rewrite<- H0.
    now asimpl.
Qed.

Lemma ψ_up_subst σ : up (σ >>> ψ) = up σ >>> ψ.
Proof.
  f_ext. destruct x ; asimpl ; try easy.
  - now rewrite ψ_ren_pres with (l:=[]).
Qed.

Lemma ψ_subst_pres :
  (forall s l σ, ψ' s.[σ] l..[σ >>> ψ] = (ψ' s l).[σ >>> ψ]).
Proof.
  induction s ; intros.
  - destruct l as [| u l] ; asimpl ; try easy.
    + now rewrite ψ_app_lemma.      
  - destruct l as [| u l] ; asimpl ; try easy.
    + rewrite ψ_up_subst.
      now rewrite<- IHs.
    + rewrite ψ_up_subst.      
      now rewrite<- IHs.   
  - asimpl. rewrite<- IHs1. asimpl. now rewrite<- IHs2.
Qed.

(* As bijecções preservam a relação de um passo *)
(* -------------------------------------------- *)

Lemma θ'_step_pres l :
  forall s s', Lambda.step s s' -> Lambda.step (θ' s l) (θ' s' l).
Proof.
  induction l as [| u l]; intros ; asimpl ; try easy.
  - fold (θ' (App s (θ u)) l).
    fold (θ' (App s' (θ u)) l).
    apply IHl. now constructor.
Qed.
    
Theorem θ_step_pres :
  (forall (t t': Canonical.term), Canonical.step t t' -> Lambda.step (θ t) (θ t'))
  /\
  (forall (l l': list Canonical.term), Canonical.step' l l' -> forall s, Lambda.step (θ' s l) (θ' s l')).
Proof.  
  apply Canonical.mut_comp_ind ; intros ; asimpl ; eauto.  
  - now constructor. 
  - apply θ'_step_pres. now constructor.
  - apply θ'_step_pres. apply Step_App1. now constructor.
  - apply θ'_step_pres. now apply Step_App2.

  - inversion b as [Beta1 | Beta2].
    + inversion Beta1 ; subst ; asimpl.
      constructor. rewrite (proj1 θ_subst_pres). now asimpl.
    + inversion Beta2 ; subst. asimpl.
      rewrite (proj1 θ_app_lemma). 
      apply θ'_step_pres. constructor. constructor.
      rewrite (proj1 θ_subst_pres). now asimpl.
  - apply θ'_step_pres. now constructor. 
Qed.

Lemma ψ_subst_rw s1 s2 :
  ψ' s1.[s2/] [] = (ψ' s1 []).[ψ' s2 []/].
Proof.
  rewrite ψ_subst_pres with (l:=[]).
  fold (ψ s1.[s2/]). fold (ψ s1). fold (ψ s2).
  autosubst.
Qed.

Theorem ψ'_step_pres :
  forall s s', Lambda.step s s' ->
          forall l, Canonical.step (ψ' s l) (ψ' s' l).
Proof.
  intros s s' H0. induction H0 ; intros ; subst.
  - asimpl.    
    destruct l as [| u l].
    + constructor. left. constructor.
      now rewrite ψ_subst_rw.
    + constructor. right. constructor.
      rewrite<- ψ_subst_rw. fold (ψ s.[t/]).
      now rewrite ψ_app_lemma.
  - destruct l as [| u l] ; asimpl.
    + constructor. apply IHstep.
    + constructor. apply IHstep.
  - asimpl. apply IHstep.
  - asimpl. repeat rewrite ψ_app_lemma.
    apply step_comp_app2. now apply IHstep.
Qed.
    
Corollary ψ_step_pres :
  forall s s', Lambda.step s s' -> Canonical.step (ψ s) (ψ s').
Proof. intros s s' H. now apply ψ'_step_pres. Qed.  

(* isomorphism at the level of types *)
(* --------------------------------- *)

Require Import SimpleTypes.

Theorem θ_is_admissible :
  forall Γ,
  (forall t A, Canonical.sequent Γ t A -> Lambda.sequent Γ (θ t) A)
  /\
  (forall A l B, list_sequent Γ A l B -> forall s, Lambda.sequent Γ s A -> Lambda.sequent Γ (θ' s l) B).
Proof.
  apply Canonical.mut_sequent_ind ; intros ; asimpl ;
    try easy ; try now constructor.
  - fold (θ' (App (Var x) (θ u)) l). apply H0.
    apply Elim with A ; try easy.
    + now constructor.
  - fold (θ' (App (Lam (θ t)) (θ u)) l). apply H1.
    apply Elim with A ; try easy.
    + now constructor.
  - fold (θ' (App s0 (θ u)) l). apply H0.
    apply Elim with A ; try easy.
Qed.        
    
Lemma ψ'_is_admissible Γ s A :
  Lambda.sequent Γ s A ->
    forall l B, list_sequent Γ A l B -> Canonical.sequent Γ (ψ' s l) B.
Proof.
  intro H. induction H ; intros.
  - inversion H0 ; subst ; asimpl ; eauto.
  - inversion H0 ; subst ; asimpl ; eauto.
  - asimpl. eauto.
Qed.  
  
Theorem ψ_is_admissible Γ s A :
  Lambda.sequent Γ s A -> Canonical.sequent Γ (ψ s) A.
Proof.
  intro H. induction H ; asimpl ; auto.
  - eapply ψ'_is_admissible ; eauto.
Qed.
