import FormalConjectures.Util.ProblemImports

noncomputable def qAll : Quot (fun (_ _ : Prop) => True) := Quot.mk _ True
#check (Quot.out qAll : Prop)
#reduce Quot.out qAll
#check Quot.out_eq qAll
example : (Quot.out qAll) := by
  -- try native/simp
  change Quot.out qAll
  -- exact True.intro
  sorry
#print axioms qAll
