
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
  : bisimF_ C X R (existT _ shape extension_l) (existT _ shape extension_r)
.

Definition bisimF (C : Container) (R : M C -> M C -> Prop) (x y : M C) :=
  bisimF_ C (M C) R (unfoldM x) (unfoldM y).

Definition bisim (C : Container) := paco2 (bisimF C).
