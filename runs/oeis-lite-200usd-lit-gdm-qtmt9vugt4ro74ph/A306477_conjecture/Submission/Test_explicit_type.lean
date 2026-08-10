inductive Ind (α : Type) (β : Type) (inst : Option β) : Type where
  | mk : (β → Empty) → Ind α β inst

def instLow (α : Type) : Option Empty :=
  Option.none

def instActive : Option (Ind Unit Empty (instLow Unit)) :=
  Option.some (Ind.mk (fun x => x))

def cast_val (y : Ind Unit (Ind Unit Empty (instLow Unit)) instActive) : Ind Unit Empty (instLow Unit) :=
  match y with
  | .mk g => .mk (fun (x : Empty) => x)

mutual
  def unsound (y : Ind Unit (Ind Unit Empty (instLow Unit)) instActive) : Empty :=
    match y with
    | .mk f => f (cast_val y)

  def f (z : Ind Unit Empty (instLow Unit)) : Empty :=
    unsound (cast_val_forward z)

  def cast_val_forward (z : Ind Unit Empty (instLow Unit)) : Ind Unit (Ind Unit Empty (instLow Unit)) instActive :=
    match z with
    | .mk g => .mk f
end
