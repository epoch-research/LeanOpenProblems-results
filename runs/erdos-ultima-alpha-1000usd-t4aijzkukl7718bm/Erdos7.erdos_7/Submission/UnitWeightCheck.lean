import FormalConjecturesUtil
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
example : (4095 : ℕ).totient = 1728 := by decide +kernel
example : ordProj[2] ((4095 : ℕ).totient) = 64 := by
  rw [← Nat.primeFactorsList_count_eq]
  decide +kernel
example : (∑ i : Fin 3, 1 / (![2,4,4] i : ℚ)) = 1 := by norm_num [Fin.sum_univ_succ]
