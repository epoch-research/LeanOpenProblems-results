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
  val := Opt.some (@Ind.mk False Unit instLow (fun x => x))

def unsound (y : @Ind (Ind Unit) Unit instActive) : False :=
  match y with
  | @Ind.mk _ _ _ f => f y
