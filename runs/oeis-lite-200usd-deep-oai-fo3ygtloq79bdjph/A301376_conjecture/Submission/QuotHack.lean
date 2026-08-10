import FormalConjectures.Util.ProblemImports

def R (a b : Bool) := True

def F : Quot R → Prop := by
  intro q
  refine Quot.inductionOn q ?_
  intro b
  exact b = true

example : False := by
  have hq : Quot.mk R false = Quot.mk R true := Quot.sound trivial
  have hf : F (Quot.mk R false) := by
    --?
    simp [F]
  have ht : F (Quot.mk R true) := by simp [F]
  -- cast?
  simp [F] at hf
