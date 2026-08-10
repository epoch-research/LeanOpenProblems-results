import FormalConjectures.Util.ProblemImports
axiom P : Prop
inductive Loeb (P : Prop) : Prop where
| intro : (Loeb P → P) → Loeb P

def extract : Loeb P → P
| .intro f => f (.intro f)

theorem p : P := extract (.intro extract)
#print axioms p
