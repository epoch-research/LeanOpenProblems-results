import FormalConjectures.Util.ProblemImports

structure S where
  x : Nat
  h : x = 37

def goodS : S := ⟨37, rfl⟩
instance : Nonempty S := ⟨goodS⟩

partial def badS : S := ⟨42, (badS).h⟩

#reduce badS.x
#eval badS.x
example : badS.x = 42 := by native_decide
-- theorem fieldProof : (42:Nat)=37 := by simpa using badS.h
#print axioms badS
