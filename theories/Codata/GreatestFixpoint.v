
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

Definition next_eq {I} (C : Container I I) (i : I) (x y : M C i)
           (command : projT1 (unfoldM x) = projT1 (unfoldM y))
           (r : Response C i (projT1 (unfoldM x))) :
  next C i (projT1 (unfoldM x)) r = next C i (projT1 (unfoldM y)) (rew command in r) :=
  J
    (fun c (command : projT1 (unfoldM x) = c) => next C i (projT1 (unfoldM x)) r = next C i c (rew command in r))
    eq_refl
    (projT1 (unfoldM y))
    command.

CoInductive bisim {I} (C : Container I I) (i : I) (x y : M C i) := fold_bisim
  { command : projT1 (unfoldM x) = projT1 (unfoldM y)
  ; response : forall r, bisim C _
                          (rew (next_eq C i x y command r) in projT2 (unfoldM x) r)
                          (projT2 (unfoldM y) (rew command in r))
  }.
