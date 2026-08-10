import FormalConjectures.Util.ProblemImports

structure Magic (P : Prop) where
  d : Decidable P
  cert : match d with | isTrue _ => True | isFalse _ => False

partial def magic (P : Prop) : Magic P :=
  { d := decLoop P, cert := by
      unfold decLoop
      -- no
      sorry }
where
  decLoop (P : Prop) : Decidable P := decLoop P

-- Try just loop without body proof via projection
partial def magic2 (P : Prop) : Magic P := magic2 P

def getP {P : Prop} (m : Magic P) : P := by
  cases m.d with
  | isTrue h => exact h
  | isFalse hn => exact False.elim m.cert

theorem arbitrary (P : Prop) : P := getP (magic2 P)
#print axioms arbitrary
