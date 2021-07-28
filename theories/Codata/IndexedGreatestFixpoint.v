
Set Primitive Projections.

From Coq Require Import
     Program.Basics.

From Paco Require Import
     paco.

From ITree Require Import
     Codata.IndexedContainer.

Import EqNotations.

Local Open Scope program_scope.

CoInductive M {I} (C : Container I I) (i : I) := foldM { unfoldM : [ C ] (M C) i }.

Arguments unfoldM {I} {C} {i}.
Arguments foldM {I} {C} {i}.

CoFixpoint anamorphism {I : Type} {C : Container I I} {X} :
  (forall i, X i -> [ C ] X i) -> (forall i, X i -> M C i) :=
  fun coalg i => foldM ∘ container_map C (anamorphism coalg) i ∘ coalg i.

Variant bisimF_ {I O} (C : Container I O) (X : I -> Type) (R : forall i, X i -> X i -> Type)
        (o : O) : [ C ] X o -> [ C ] X o -> Prop :=
| BisimStep (command : Command C o)
            (extension_l extension_r : forall r, X (next C command r))
            (REL : forall r, R (next C command r) (extension_l r) (extension_r r))
  : bisimF_ C X R o (existT _ command extension_l) (existT _ command extension_r)
.

Lemma bisimF_intro {I O} {C : Container I O} {X : I -> Type}
      {R : forall i, X i -> X i -> Type} {o : O} :
      forall command : Command C o,
      forall extension_l extension_r : forall r, X (next C command r),
      (forall r, R (next C command r) (extension_l r) (extension_r r)) ->
      bisimF_ C X R o (existT _ command extension_l) (existT _ command extension_r).
Proof.
  exact (BisimStep C X R o).
Qed.

Lemma bisimF_elim {I O} {C : Container I O} {X : I -> Type}
      {R : forall i, X i -> X i -> Type} {o : O} {lhs rhs} :
      bisimF_ C X R o lhs rhs ->
      exists (command : Command C o)
             (extension_l extension_r : forall r, X (next C command r))
             (REL : forall r, R (next C command r) (extension_l r) (extension_r r)),
             lhs = existT _ command extension_l /\ rhs = existT _ command extension_r.
Proof.
  intros [command extension_l extension_r REL].
  exists command, extension_l, extension_r, REL.
  split; reflexivity.
Qed.

Definition bisimF {I} (C : Container I I) (R : forall i, M C i -> M C i -> Prop) (i : I) (x y : M C i) :=
  bisimF_ C (M C) R i (unfoldM x) (unfoldM y).

Lemma monotone3_bisimF {I} (C : Container I I) :
  monotone3 (bisimF C).
Proof.
  apply monotone3_eq.
  intros R1 R2 LE i x y Hb.
  destruct (bisimF_elim Hb) as [command [extension_l [extension_r [REL [H1 H2]]]]].
  unfold bisimF.
  rewrite H1, H2.
  apply (bisimF_intro command).
  intros r.
  apply LE.
  exact (REL r).
Qed.

Definition bisim {I} (C : Container I I) := paco3 (bisimF C).
