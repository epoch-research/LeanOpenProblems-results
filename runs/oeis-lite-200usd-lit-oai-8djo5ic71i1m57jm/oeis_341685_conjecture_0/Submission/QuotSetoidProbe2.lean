import FormalConjectures.Util.ProblemImports

-- Can Setoid be used to extract an arbitrary proposition from quotient equality?
-- This attempts the common triangle trick; it should fail at transitivity.
def P : Prop := False
inductive A | a | b | c deriving DecidableEq
open A

def R : A → A → Prop
| a, b => P
| b, a => P
| _, _ => True

example : Equivalence R := by
  constructor
  · intro x; cases x <;> trivial
  · intro x y h; cases x <;> cases y <;> simp [R] at *; assumption
  · intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp [R] at *

-- If the above worked, exact from quotient equality would prove P.
