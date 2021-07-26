
Record Container (I O : Type) : Type := container
  { Command : O -> Type
  ; Response : forall {o : O}, Command o -> Type
  ; next : forall {o : O} (c : Command o), Response c -> I
  }.

Arguments Command {I} {O}.
Arguments Response {I} {O}.
Arguments next {I} {O}.

Definition container_ext {I O} (C : Container I O) : (I -> Type) -> (O -> Type) :=
  fun X o => {c : C.(Command) o & forall (r : C.(Response) o c), X (C.(next) o c r)}.

Notation "[ C ]" := (container_ext C) (at level 99, no associativity).

Definition container_map {I} (C : Container I I) {X Y : I -> Type} :
  (forall i, X i -> Y i) -> (forall i, [ C ] X i -> [ C ] Y i) :=
  fun f i x => let (c , g) := x in existT _ c (fun r => f _ (g r)).
