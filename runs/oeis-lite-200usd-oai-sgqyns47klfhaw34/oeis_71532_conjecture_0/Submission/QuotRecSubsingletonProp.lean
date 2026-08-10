import FormalConjectures.Util.ProblemImports

def Q := Quot (fun _ _ : Prop => True)

def q (P : Prop) : Q := Quot.mk _ P

-- Try direct proposition-valued family
noncomputable def Fam (x : Q) : Prop :=
  Quot.recOnSubsingleton x (fun P : Prop => P)

#check Fam
#reduce Fam (q True)
#reduce Fam (q False)

example (P : Prop) : P := by
  have hq : q True = q P := Quot.sound True.intro
  have ht : Fam (q True) := True.intro
  exact Eq.mp (by rw [hq]) ht

#print axioms Fam
#print axioms _example
