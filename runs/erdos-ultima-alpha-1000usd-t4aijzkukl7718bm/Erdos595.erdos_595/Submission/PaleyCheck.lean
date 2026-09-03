import Submission.TriangleHit
open scoped BigOperators
#check WithLp.toLp
#check PiLp.inner_apply
#check EuclideanSpace
#check real_inner_self_eq_norm_sq
example : inner ℝ (WithLp.toLp 2 (![1/2,1/2,1/2,1/2] : Fin 4 → ℝ))
    (WithLp.toLp 2 (![1/2,1/2,1/2,1/2] : Fin 4 → ℝ)) = 1 := by
  norm_num [PiLp.inner_apply, Fin.sum_univ_succ]
