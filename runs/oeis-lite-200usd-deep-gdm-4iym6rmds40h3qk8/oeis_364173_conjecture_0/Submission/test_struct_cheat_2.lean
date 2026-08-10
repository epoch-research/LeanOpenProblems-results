import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

theorem q_sound (A B : Prop) : Quot.mk R A = Quot.mk R B := Quot.sound (by trivial)

-- We can map Q to Prop:
noncomputable def lift_prop : Q → Prop := Quot.lift (fun _ => True) (by intro a b h; rfl)

-- Let's define a function on Q to our type:
def P (x : Q) : Prop := answer(sorry)

-- wait, can we define a theorem with P?
theorem P_eq (x y : Q) : P x = P y := by
  unfold P
  -- Wait, answer(sorry) evaluates to True in Prop
  rfl

#print axioms P_eq
