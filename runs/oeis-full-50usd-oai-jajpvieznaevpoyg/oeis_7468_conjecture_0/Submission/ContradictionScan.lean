import FormalConjectures.Util.ProblemImports

-- Try common contradiction lemmas with synthesized assumptions.
#check false_of_nontrivial_of_subsingleton
#check Finite.false
#check Infinite.false
#check Nat.Prime.not_isSquare

-- examples that should not synthesize conflicting assumptions
-- theorem bad1 : False := false_of_nontrivial_of_subsingleton ℕ
-- theorem bad2 : False := Finite.false (α := ℕ) inferInstance
-- theorem bad3 : False := Infinite.false (α := Fin 0) inferInstance
