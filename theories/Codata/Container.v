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

Definition Ext C {X} (s : Shape C) (g : Position C s -> X) : [ C ] X := existT _ s g.
Definition shape {C} {X} (cx : [ C ] X) : Shape C := projT1 cx.
Definition get {C} {X} (cx : [ C ] X) : Position C (shape cx) -> X := projT2 cx.

Definition container_map (C : Container) {X Y : Type} :
  (X -> Y) -> ([ C ] X -> [ C ] Y) :=
  fun f x => Ext C (shape x) (f ∘ get x).
