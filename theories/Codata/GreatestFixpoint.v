
Set Primitive Projections.

From Coq Require Import
     Program.Basics.

From Paco Require Import
     paco.

From ITree Require Import
     Codata.Container.

Import EqNotations.

Local Open Scope program_scope.

CoInductive M {I} (C : Container I I) (i : I) := foldM { unfoldM : [ C ] (M C) i }.

Arguments unfoldM {I} {C} {i}.
Arguments foldM {I} {C} {i}.

CoFixpoint anamorphism {I : Type} {C : Container I I} {X} :
  (forall i, X i -> [ C ] X i) -> (forall i, X i -> M C i) :=
  fun coalg i => foldM ∘ container_map C (anamorphism coalg) i ∘ coalg i.

Definition J {A : Type} {x : A} (P : forall y : A, x = y -> Type) (d : P x eq_refl) (y : A) (p : x = y) : P y p :=
  match p in _ = y return P y p with
  | eq_refl => d
  end.

Definition next_eq {I O} {C : Container I O} {X Y : I -> Type}
           {o : O} {x : [ C ] X o} {y : [ C ] Y o}
           (command : projT1 x = projT1 y)
           (r : Response C (projT1 x)) :
  next C (projT1 x) r = next C (projT1 y) (rew command in r) :=
  J
    (fun c (command : projT1 x = c) => next C (projT1 x) r = next C c (rew command in r))
    eq_refl
    (projT1 y)
    command.

Variant bisimF_ {I O} (C : Container I O) (X Y : I -> Type) (R : forall i, X i -> Y i -> Type)
        (o : O) (x : [ C ] X o) (y : [ C ] Y o) : Prop :=
| BisimStep (command_eq : projT1 x = projT1 y)
            (response_R : forall r, R (next C (projT1 y) (rew command_eq in r))
                                 (rew (next_eq command_eq r) in (projT2 x r))
                                 (projT2 y (rew command_eq in r)))
.

Definition bisimF {I} (C : Container I I) (R : forall i, M C i -> M C i -> Prop) (i : I) (x : M C i) (y : M C i) :=
  bisimF_ C (M C) (M C) R i (unfoldM x) (unfoldM y).

Definition bisim {I} (C : Container I I) := paco3 (bisimF C).
