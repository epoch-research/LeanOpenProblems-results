import FormalConjecturesUtil

example :
    ({ n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2)) =
      Filter.Tendsto
        (fun N : ℕ =>
          ((({n : ℕ | Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)} ∩
            Set.Iio N).ncard : ℝ) / (N : ℝ)))
        Filter.atTop (nhds ((1 : ℝ) / 2)) := by
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter,
    Nat.ncard_Iio]

example : (Filter.atTop : Filter ℕ).NeBot := inferInstance
example : (1 / 2 : ℝ) ≠ 0 := by norm_num
#print axioms Nat.prime_maxPrimeFac_of_one_lt
#print axioms Nat.maxPrimeFac_dvd
#print axioms Nat.le_maxPrimeFac
