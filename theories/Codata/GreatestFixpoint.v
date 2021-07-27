
Set Primitive Projections.

From ITree Require Import
     Codata.Container.

From Coq Require Import
     Program.Basics.

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

Definition next_eq {I O} (C : Container I O) (X Y : I -> Type)
           (o : O)
           (x : [ C ] X o) (y : [ C ] Y o)
           (command : projT1 x = projT1 y)
           (r : Response C o (projT1 x)) :
  next C o (projT1 x) r = next C o (projT1 y) (rew command in r) :=
  J
    (fun c (command : projT1 x = c) => next C o (projT1 x) r = next C o c (rew command in r))
    eq_refl
    (projT1 y)
    command.

Variant bisimF {I O} (C : Container I O) (X Y : I -> Type) (R : forall i, X i -> Y i -> Type)
        (o : O) (x : [ C ] X o) (y : [ C ] Y o) :=
| BisimStep (command_eq : projT1 x = projT1 y)
            (response_R : forall r, R (next C o (projT1 y) (rew command_eq in r))
                                  (rew (next_eq C X Y o x y command_eq r) in (projT2 x r))
                                  (projT2 y (rew command_eq in r)))
.

CoInductive bisim {I} (C : Container I I) (i : I) (x y : M C i) : Type := fold_bisim
  { unfold_bisim : bisimF C (M C) (M C) (bisim C) i (unfoldM x) (unfoldM y) }.
