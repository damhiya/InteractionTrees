From Coq Require Import
     Program.Basics.

Local Open Scope program_scope.

Record Container : Type := container
  { Shape : Type
  ; Position : Shape -> Type
  }.

Definition container_ext (C : Container) : Type -> Type :=
  fun X => {s : Shape C & Position C s -> X}.

Notation "[ C ]" := (container_ext C) (at level 99, no associativity).

Definition container_map (C : Container) {X Y : Type} :
  (X -> Y) -> ([ C ] X -> [ C ] Y) :=
  fun f x => existT _ (projT1 x) (f ∘ projT2 x).
