import FormalConjectures.Util.ProblemImports

def rNat (a b : Nat) := True
inductive K : Quot rNat → Type where
| c0 : K (Quot.mk rNat 0)
| c1 : K (Quot.mk rNat 1)

def e01 : Quot.mk rNat 0 = Quot.mk rNat 1 := Quot.sound True.intro
def c0as1 : K (Quot.mk rNat 1) := Eq.mp (congrArg K e01) K.c0

#check K.noConfusion
#check K.c0.noConfusion
#check K.c1.noConfusion

example : c0as1 ≠ K.c1 := by
  intro h
  cases h

example : False := by
  -- If subsingleton? no
  have h : c0as1 = K.c1 := by
    -- try proof irrelevance? no
    sorry
  exact (by cases h)
