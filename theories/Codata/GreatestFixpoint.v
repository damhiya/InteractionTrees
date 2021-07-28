
Set Primitive Projections.

From Coq Require Import
     Program.Basics.

From Paco Require Import
     paco.

From ITree Require Import
     Codata.Container.

Import EqNotations.

Local Open Scope program_scope.

CoInductive M (C : Container) := foldM { unfoldM : [ C ] (M C) }.

Arguments unfoldM {C}.
Arguments foldM {C}.

CoFixpoint anamorphism {C : Container} {X} :
  (X -> [ C ] X) -> (X -> M C) :=
  fun coalg => foldM ∘ container_map C (anamorphism coalg) ∘ coalg.

Variant bisimF_ (C : Container) (X : Type) (R : X -> X -> Type) : [ C ] X -> [ C ] X -> Prop :=
| BisimStep (shape : Shape C)
            (extension_l extension_r : Position C shape -> X)
            (REL : forall p, R (extension_l p) (extension_r p))
  : bisimF_ C X R (Ext shape extension_l) (Ext shape extension_r)
.

Lemma bisimF_intro {C : Container} {X : Type} {R : X -> X -> Type} :
  forall shape : Shape C,
  forall extension_l extension_r : Position C shape -> X,
  (forall p, R (extension_l p) (extension_r p)) ->
  bisimF_ C X R (Ext shape extension_l) (Ext shape extension_r).
Proof.
  exact (BisimStep C X R).
Qed.

Lemma bisimF_elim {C : Container} {X : Type} {R : X -> X -> Type} {lhs rhs} :
  bisimF_ C X R lhs rhs ->
  exists (shape : Shape C)
         (extension_l extension_r : Position C shape -> X)
         (REL : forall p, R (extension_l p) (extension_r p)),
         lhs = Ext shape extension_l /\ rhs = Ext shape extension_r.
Proof.
  intros [shape extension_l extension_r REL].
  exists shape, extension_l, extension_r, REL.
  split; reflexivity.
Qed.

Definition bisimF (C : Container) (R : M C -> M C -> Prop) (x y : M C) :=
  bisimF_ C (M C) R (unfoldM x) (unfoldM y).

Lemma monotone2_bisimF (C : Container) :
  monotone2 (bisimF C).
Proof.
  apply monotone2_eq.
  intros R1 R2 LE x y Hb.
  destruct (bisimF_elim Hb) as [shape [extension_l [extension_r [REL [H1 H2]]]]].
  unfold bisimF.
  rewrite H1, H2.
  apply (bisimF_intro shape).
  intros p.
  apply LE.
  exact (REL p).
Qed.

Definition bisim (C : Container) := paco2 (bisimF C).
