import FormalConjectures.Util.ProblemImports
#check Int.cast_surjective
#check Int.cast_injective
#check Int.cast_inj
#check Real.instNontrivial
#check Subsingleton ℝ
#check subsingleton_or_nontrivial ℝ
example : Nontrivial ℝ := inferInstance
-- search by exact?
example : Function.Surjective (fun z : ℤ => (z : ℝ)) := by
  exact?
