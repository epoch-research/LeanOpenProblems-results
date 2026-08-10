import FormalConjectures.Util.ProblemImports

namespace QuotIndexedDeriveSubsingletonExplore

def Q := Quot (fun (_ _ : Bool) => True)

inductive I : Q → Type where
| left : I (Quot.mk _ false)
| right : I (Quot.mk _ true)
deriving DecidableEq

-- Try deriving manually after declaration.
-- deriving instance Subsingleton for I

def leftAtTrue : I (Quot.mk _ true) := by
  have h : Quot.mk (fun (_ _ : Bool) => True) false = Quot.mk _ true := Quot.sound trivial
  exact h ▸ I.left

#check instDecidableEqI

example : leftAtTrue ≠ I.right := by
  intro h
  cases h

example : False := by
  have h : leftAtTrue = I.right := by decide
  have hn : leftAtTrue ≠ I.right := by
    intro h; cases h
  exact hn h

#print axioms leftAtTrue
end QuotIndexedDeriveSubsingletonExplore
