import FormalConjectures.Util.ProblemImports

namespace CharOneBool

def mul (a b : Bool) := b
instance : Mul Bool := ⟨mul⟩
instance : Zero Bool := ⟨false⟩
instance : One Bool := ⟨false⟩
instance : Add Bool := ⟨fun _ b => b⟩
instance : NatCast Bool := ⟨fun _ => false⟩

-- Try manually constructing minimal semiring
instance instNAS : NonAssocSemiring Bool where
  zero := false
  one := false
  add := fun _ b => b
  mul := fun _ b => b
  nsmul := fun _ b => b
  npow := fun _ b => b
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  natCast := fun _ => false
  natCast_zero := rfl
  natCast_succ := by intro n; rfl

instance : Nontrivial Bool := ⟨⟨false,true, by decide⟩⟩

example : False := by
  haveI : CharP Bool 1 := inferInstance
  exact CharP.false_of_nontrivial_of_char_one (R:=Bool)

end CharOneBool
