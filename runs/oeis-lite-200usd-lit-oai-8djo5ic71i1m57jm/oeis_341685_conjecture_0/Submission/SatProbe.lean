import FormalConjectures.Util.ProblemImports

#check Sat.Fmla.refute
#check Sat.Fmla.proof
#check Sat.Fmla.reify
#check Sat.Fmla.false
#check Sat.Fmla.not
#check Sat.Fmla.and
#check Sat.Fmla.proof

example : False := by
  -- see if aesop can abuse SAT
  -- exact Sat.Fmla.refute ?f ?h1 ?h2
  aesop
