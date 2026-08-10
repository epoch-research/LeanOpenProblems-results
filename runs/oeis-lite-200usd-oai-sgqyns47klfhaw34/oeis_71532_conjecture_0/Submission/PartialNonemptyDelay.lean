import FormalConjectures.Util.ProblemImports

inductive Delay (P : Prop) where
| later : Delay P → Delay P

partial def neDelay (P : Prop) : Nonempty (Delay P) := ⟨Delay.later (Classical.choice (neDelay P))⟩

noncomputable instance (P : Prop) : Nonempty (Delay P) := neDelay P

-- Recursor into False for Delay False?
def noDelayFalse : Delay False -> False
| .later d => noDelayFalse d

example : False := noDelayFalse (Classical.choice (neDelay False))
#print axioms neDelay
#print axioms noDelayFalse
#print axioms PartialNonemptyDelay._example_1
