import FormalConjectures.Util.ProblemImports

abbrev Q := Quot (fun a b : Prop => a)
def q (P : Prop) : Q := Quot.mk _ P

#check Quot.out_eq (q True)
#check Quot.exact (Quot.out_eq (q True))

example : Quot.out (q True) := by
  -- try cases on exact proof
  let h := Quot.exact (Quot.out_eq (q True))
  change EqvGen (fun a b : Prop => a) (Quot.out (q True)) True at h
  -- exact?
  cases h with
  | rel hrel => exact hrel
  | refl => trivial
  | symm h => sorry
  | trans h1 h2 => sorry

#print axioms q
