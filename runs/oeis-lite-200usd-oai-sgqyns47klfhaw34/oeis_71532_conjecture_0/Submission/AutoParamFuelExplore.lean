import FormalConjectures.Util.ProblemImports

-- A function whose proof argument has an auto tactic that calls the function with explicit proof at smaller fuel.
def f (P : Prop) : (fuel : Nat) → (h : P := by
  -- goal P, context includes P and fuel? try calling f P 0 recursively
  exact f P 0) → P
| _, h => h

-- Calling f P 0 triggers autoParam exact f P 0 -> recursion in elaborator likely.
theorem arbitrary (P : Prop) : P := f P 0
#print axioms arbitrary
#print f
