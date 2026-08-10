import FormalConjectures.Util.ProblemImports
#check Real.goldenConj
#print Real.goldenConj
#check goldConj_irrational
#print goldConj_irrational
#print axioms goldConj_irrational
example : Irrational Real.goldenConj := goldConj_irrational
example : ¬ ∃ q : ℚ, (q : ℝ) = Real.goldenConj := goldConj_irrational
-- Try prove rationality by norm_num/simp from definition
example : ∃ q : ℚ, (q : ℝ) = Real.goldenConj := by
  unfold Real.goldenConj
  apply?
