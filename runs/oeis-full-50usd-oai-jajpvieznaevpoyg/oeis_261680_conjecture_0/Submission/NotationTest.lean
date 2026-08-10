import FormalConjectures.Util.ProblemImports

def aa (n : ℕ) := n
macro_rules (kind := term_>_)
  | `($x:term > $y:term) => `(True)
example (n : ℕ) : aa n > 0 := by
  trivial
#print NotationTest._example_1
