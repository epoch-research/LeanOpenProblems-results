import Submission.AffineCompactnessReduction
example (K : Type*) (u : Fin 4 → K) : u (3+1) = u 0 := by simp +decide
example : ¬ ((2 : Fin 4)=0) := by decide
example (K : Type*) [Field K] (v a : Fin 4 → K) (h : v (3+1) = a 3*v 3+(1-a 3)*(if (3:Fin 4)=0 then 1 else 0)) : v 0 = a 3*v 3 := by
  simpa +decide using h
