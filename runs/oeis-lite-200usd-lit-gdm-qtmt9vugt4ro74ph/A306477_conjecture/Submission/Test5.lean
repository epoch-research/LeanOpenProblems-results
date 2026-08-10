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

def cast_val : Ind Unit → @Ind False Unit instLow
  | @Ind.mk _ _ _ g => @Ind.mk False Unit instLow (fun (x : False) => x)

def unsound (y : Ind Unit) : False :=
  match y with
  | @Ind.mk _ _ _ f => f (cast_val y)

mutual
  def cast_val_forward (x : @Ind False Unit instLow) : Ind Unit :=
    @Ind.mk (@Ind False Unit instLow) Unit instActive unsound_low

  def unsound_low (z : @Ind False Unit instLow) : False :=
    unsound (cast_val_forward z)
end

def unsound_direct : False :=
  match h : instActive.val with
  | Opt.some x => unsound_low x
  | Opt.none => by
      have h_eq : instActive.val = Opt.some (Ind.mk (inst := instLow) (fun x => x)) := rfl
      rw [h_eq] at h
      contradiction
