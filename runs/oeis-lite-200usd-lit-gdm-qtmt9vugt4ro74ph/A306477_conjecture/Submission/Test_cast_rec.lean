inductive Opt (p : Prop) : Type where
  | none : Opt p
  | some : p → Opt p

structure Bad (α : Type) : Type where
  β : Prop
  val : Opt β

inductive Ind (α : Type) (inst : Bad α) : Prop where
  | mk : (inst.β → False) → Ind α inst

def instLow (α : Type) : Bad α :=
  ⟨False, Opt.none⟩

def instActive : Bad Unit :=
  ⟨Ind Unit (instLow Unit), Opt.some (Ind.mk (inst := instLow Unit) (fun x => x))⟩

def unsound : Ind Unit instActive → False
  | Ind.mk g => g (Ind.mk (fun x => x))

def cast_val_forward : Ind Unit (instLow Unit) → Ind Unit instActive
  | Ind.mk g => Ind.mk (fun (x : instActive.β) => unsound (cast_val_forward x))
