import FormalConjectures.Util.ProblemImports
noncomputable def rep (P : Prop) : Prop := Quot.out (Quot.mk (fun (_ _ : Prop)=>True) P)
#reduce rep False
#check Quot.out_eq (Quot.mk (fun (_ _ : Prop)=>True) False)
example (P : Prop) : rep P := by
  unfold rep
  -- exact ?
  sorry
example (P : Prop) : rep P = P := by
  unfold rep
  --
  sorry
