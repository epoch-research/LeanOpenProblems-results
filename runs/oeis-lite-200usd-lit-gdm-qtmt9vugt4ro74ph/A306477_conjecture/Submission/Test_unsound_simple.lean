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

def val_low : Ind Unit (instLow Unit) :=
  match instActive.val with
  | Opt.some x => x

def unsound (y : Ind Unit instActive) : False :=
  match y with
  | Ind.mk f => f val_low

def val_active : Ind Unit instActive :=
  Ind.mk unsound

def proof_of_false : False :=
  unsound val_active
