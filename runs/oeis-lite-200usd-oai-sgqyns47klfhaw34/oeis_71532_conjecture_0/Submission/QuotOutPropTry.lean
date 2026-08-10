import FormalConjectures.Util.ProblemImports

def univRel (p q : Prop) := True
noncomputable def qtrue : Quot univRel := Quot.mk univRel True
noncomputable def qfalse : Quot univRel := Quot.mk univRel False
#check Quot.sound (r:=univRel) (a:=True) (b:=False) True.intro
#check congrArg (@Quot.out Prop univRel) (Quot.sound (r:=univRel) (a:=True) (b:=False) True.intro)
#check (Quot.out qtrue : Prop)
#reduce (Quot.out qtrue : Prop)
#check Quot.out_eq qtrue
-- Try prove out qtrue
example : Quot.out qtrue := by
  -- no obvious
  sorry
