From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

Proposition multistep_trans (A: Type) (R: relation A):
  forall x y z, clos_refl_trans_1n _ R x y -> clos_refl_trans_1n _ R y z ->
            clos_refl_trans_1n _ R x z.
Proof.                                                  
  intros.
  induction H.
  - easy.
  - eapply rt1n_trans ; eauto.
Qed.
