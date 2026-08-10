inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) (β : Prop) : Type where
  val : Opt β

inductive Ind (α : Type) (β : Prop) (inst : Bad α β) : Type where
  | mk : (β → False) → Ind α β inst

def instLow (α : Type) : Bad α False :=
  ⟨Opt.none⟩

def instActive : Bad Unit (Ind Unit False (instLow Unit)) :=
  ⟨Opt.some (Ind.mk (fun x => x))⟩

def cast_val (y : Ind Unit (Ind Unit False (instLow Unit)) instActive) : Ind Unit False (instLow Unit) :=
  match y with
  | .mk g => .mk (fun (x : False) => x)

mutual
  def unsound (y : Ind Unit (Ind Unit False (instLow Unit)) instActive) : False :=
    match y with
    | .mk f => f (cast_val y)

  def f (z : Ind Unit False (instLow Unit)) : False :=
    unsound (cast_val_forward z)

  def cast_val_forward (z : Ind Unit False (instLow Unit)) : Ind Unit (Ind Unit False (instLow Unit)) instActive :=
    match z with
    | .mk g => .mk f
end
