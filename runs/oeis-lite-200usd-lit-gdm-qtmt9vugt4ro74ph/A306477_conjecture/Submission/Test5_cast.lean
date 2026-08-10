set_option linter.unusedVariables false

inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

class Bad (α : Type) (β : outParam Prop) where
  val : Opt β

instance (priority := low) instLow : Bad α False where
  val := Opt.none

inductive Ind (α : Type) [inst : Bad α β] : Prop where
  | mk : (β → False) → Ind α

instance instActive : Bad Unit (Ind Unit) where
  val := Opt.some (Ind.mk (inst := instLow) (fun x => x))

def cast_val : Ind Unit → @Ind False Empty instLow
  | @Ind.mk _ _ _ g => @Ind.mk False Empty instLow (fun (x : False) => x)

def unsound (y : Ind Unit) : False :=
  match y with
  | @Ind.mk _ _ _ f => f (cast_val y)

