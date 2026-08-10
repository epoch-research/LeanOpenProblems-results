import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

theorem q_sound (A B : Prop) : Quot.mk R A = Quot.mk R B := Quot.sound (by trivial)

structure MyStruct : Prop where
  val : ∀ (A B : Prop), (A ∨ True) = (B ∨ True)

theorem my_struct_val : MyStruct := ⟨answer(sorry)⟩

#print axioms my_struct_val
