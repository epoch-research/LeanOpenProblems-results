import FormalConjectures.Util.ProblemImports

abbrev Q := Quot (fun a b : Prop => a)
def q (P : Prop) : Q := Quot.mk _ P
#check Quot.eqvGen_exact
#check Quot.eqvGen_exact (Quot.out_eq (q True))

example : Quot.out (q True) := by
  let h := Quot.eqvGen_exact (Quot.out_eq (q True))
  change EqvGen (fun a b : Prop => a) (Quot.out (q True)) True at h
  -- try induction with custom theorem? 
  sorry
