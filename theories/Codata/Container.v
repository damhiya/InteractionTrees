From Coq Require Import
     Program.Basics.

Local Open Scope program_scope.

Record Container : Type := container
  { Shape : Type
  ; Position : Shape -> Type
  }.

Record Extension (C : Container) (X : Type) : Type := Ext
  { shape : Shape C
  ; get : Position C shape -> X
  }.

Notation "[ C ]" := (Extension C) (at level 0, no associativity) : type_scope.
Arguments Ext {C} {X}.
Arguments shape {C} {X}.
Arguments get {C} {X}.

Definition container_map (C : Container) {X Y : Type} :
  (X -> Y) -> ([ C ] X -> [ C ] Y) :=
  fun f x => Ext (shape x) (f ∘ get x).
