
From Paco Require Import paco.

Definition Chain (X Y : Type) := X -> Y -> forall P : Type, (P -> X) -> (P -> Y) -> Type.

Variant simulationF {X Y} (R : Chain X Y) vclo (sim : X -> Y -> Prop) : X -> Y -> Prop :=
| Step t1 t2 P k1 k2
       (REL : R t1 t2 P k1 k2)
       (RELS : forall p : P, vclo sim (k1 p) (k2 p))
  : simulationF R vclo sim t1 t2
.

Definition simulation {X Y} (R : Chain X Y) vclo := paco2 (simulationF R vclo).
