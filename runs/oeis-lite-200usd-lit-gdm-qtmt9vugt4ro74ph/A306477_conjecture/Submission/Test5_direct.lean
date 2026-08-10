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

def proof_of_false : False :=
  match h : instActive.val with
  | Opt.some x =>
    match x with
    | @Ind.mk False Unit instLow f => f x
  | Opt.none => by
      have h_eq : instActive.val = Opt.some (Ind.mk (inst := instLow) (fun x => x)) := rfl
      rw [h_eq] at h
      contradiction

#check @Ind.mk
