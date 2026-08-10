import FormalConjectures.Util.ProblemImports

universe u

def Q : Sort 1 := Quot (fun (_ _ : Prop) => True)

def q (P : Prop) : Q := Quot.mk _ P

inductive I : Q → Prop where
| intro {P : Prop} (p : P) : I (q P)

-- Can extract?
def extract {P : Prop} : I (q P) → P := by
  intro h
  cases h with
  | intro p => exact p

-- Transport True to P
example (P : Prop) : P := by
  have e : q True = q P := Quot.sound trivial
  have ht : I (q True) := I.intro True.intro
  exact extract (e ▸ ht)

#print axioms QuotInductiveMinimal._example_1
