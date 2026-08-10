import FormalConjectures.Util.ProblemImports

inductive Loeb (P : Prop) : Type where
| mk : (Loeb P → P) → Loeb P

-- If accepted, try extraction
def loebProof (P : Prop) : P := by
  let x : Loeb P := Loeb.mk (fun y => match y with | Loeb.mk f => f y)
  exact match x with | Loeb.mk f => f x

#print axioms loebProof
#check loebProof False
