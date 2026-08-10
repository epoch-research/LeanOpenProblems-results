import FormalConjectures.Util.ProblemImports

inductive Delay (P : Prop) where
| later : Delay P → Delay P

partial def loopDelay (P : Prop) : Delay P := Delay.later (loopDelay P)

-- Recursor into arbitrary motive maybe can produce P from infinite loop?
def extract (P : Prop) : Delay P → P := by
  intro d
  induction d with
  | later d ih => exact ih

theorem arbitrary (P : Prop) : P := extract P (loopDelay P)
#print axioms loopDelay
#print axioms extract
#print axioms arbitrary
#reduce extract False (loopDelay False)
