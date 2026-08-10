import FormalConjectures.Util.ProblemImports

def rNat (a b : Nat) := True
inductive K : Quot rNat → Type where
| c0 : K (Quot.mk rNat 0)
| c1 : K (Quot.mk rNat 1)

def e01 : Quot.mk rNat 0 = Quot.mk rNat 1 := Quot.sound True.intro
def c0as1 : K (Quot.mk rNat 1) := Eq.mp (congrArg K e01) K.c0

example (q : Quot rNat) : Subsingleton (K q) := by
  constructor
  intro x y
  cases x <;> cases y
  · rfl
  · -- c0 c1 with indices maybe eq? goal?
    simp
  · simp
  · rfl

example : False := by
  haveI : Subsingleton (K (Quot.mk rNat 1)) := by
    constructor
    intro x y
    cases x <;> cases y <;> try rfl <;> simp
  have h : c0as1 = K.c1 := Subsingleton.elim _ _
  cases h
