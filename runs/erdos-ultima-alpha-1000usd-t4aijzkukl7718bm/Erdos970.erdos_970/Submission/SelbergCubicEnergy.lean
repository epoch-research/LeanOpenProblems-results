import Submission.SelbergNormalizerProfile
import Submission.PrimeSharpLogMoments

/-! A sharper logarithmic energy estimate for the truncated linear Selberg
profile. This development targets a cubic, not a quadratic, Jacobsthal bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma max_sub_max_eq_min (x v : ℝ) (hv : 0 ≤ v) :
    max x 0 - max (x - v) 0 = min v (max x 0) := by
  by_cases hx : x ≤ 0
  · rw [max_eq_right hx, max_eq_right (by linarith : x - v ≤ 0), min_eq_right hv]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ x)]
    by_cases hxv : x ≤ v
    · rw [max_eq_right (by linarith : x - v ≤ 0), min_eq_right hxv]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ x - v), min_eq_left (by linarith : v ≤ x)]
      ring

lemma softProfile_difference_eq_min (p : ι → ℕ) (L : ℝ) (Q : Finset ι)
    (i : ι) (hi : i ∉ Q) :
    softProfile (fun i => log (p i : ℝ)) L Q -
      softProfile (fun i => log (p i : ℝ)) L (insert i Q) =
        min (log (p i : ℝ)) (softProfile (fun i => log (p i : ℝ)) L Q) := by
  unfold softProfile
  rw [sum_insert hi]
  have he : L - (log (p i : ℝ) + ∑ j ∈ Q, log (p j : ℝ)) =
      (L - ∑ j ∈ Q, log (p j : ℝ)) - log (p i : ℝ) := by ring
  rw [he]
  exact max_sub_max_eq_min _ _ (log_natCast_nonneg _)

lemma prime_soft_dirichlet_coordinate (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (L : ℝ) (hL : 0 ≤ L) (i : ι) :
    (∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
      (softProfile (fun i => log (p i : ℝ)) L Q -
        softProfile (fun i => log (p i : ℝ)) L (insert i Q)) ^ 2) ≤
      (65 / 64) * (L * min (log (p i : ℝ)) L ^ 2 - (2 / 3) * min (log (p i : ℝ)) L ^ 3) +
        normalizerOffset 65 * min (log (p i : ℝ)) L ^ 2 := by
  let v := min (log (p i : ℝ)) L
  have hv : 0 ≤ v := le_min (log_natCast_nonneg _) hL
  have hvL : v ≤ L := min_le_right _ _
  have hcap (Q : Finset ι) :
      min (log (p i : ℝ)) (softProfile (fun i => log (p i : ℝ)) L Q) =
        min v (softProfile (fun i => log (p i : ℝ)) L Q) := by
    have hh := softProfile_le (fun i => log (p i : ℝ)) (fun i => log_natCast_nonneg _) L hL Q
    dsimp [v]
    rw [min_assoc, min_eq_right hh]
  calc
    _ = ∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
        min v (softProfile (fun i => log (p i : ℝ)) L Q) ^ 2 := by
      apply sum_congr rfl
      intro Q hQ
      rw [softProfile_difference_eq_min p L Q i (not_mem_of_erase_powerset hQ), hcap]
    _ ≤ ∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q *
        min v (softProfile (fun i => log (p i : ℝ)) L Q) ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro Q hQ hn
      exact mul_nonneg (weight_pos _ (prime_marginals p hp) Q).le (sq_nonneg _)
    _ ≤ _ := by
      exact capped_square_upper (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p)
        (primeLogLocation_nonneg p) L v (65 / 64) (normalizerOffset 65) hv hvL
        (fun t ht => cumulative_prime_upper p hp hinj t ht.1)

noncomputable def cappedLogMoment (p : ι → ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  ∑ i, min (log (p i : ℝ)) L ^ n / (p i : ℝ)

lemma prime_soft_dirichlet_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (L : ℝ) (hL : 0 ≤ L) :
    (∑ i, (1 / (p i : ℝ)) * ∑ Q ∈ (univ.erase i).powerset,
      weight (fun i => 1 / (p i : ℝ)) Q *
        (softProfile (fun i => log (p i : ℝ)) L Q -
          softProfile (fun i => log (p i : ℝ)) L (insert i Q)) ^ 2) ≤
      (65 / 64) * (L * cappedLogMoment p L 2 - (2 / 3) * cappedLogMoment p L 3) +
        normalizerOffset 65 * cappedLogMoment p L 2 := by
  calc
    _ ≤ ∑ i, (1 / (p i : ℝ)) *
        ((65 / 64) * (L * min (log (p i : ℝ)) L ^ 2 - (2 / 3) * min (log (p i : ℝ)) L ^ 3) +
          normalizerOffset 65 * min (log (p i : ℝ)) L ^ 2) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (prime_soft_dirichlet_coordinate p hp hinj L hL i) (by positivity)
    _ = _ := by
      unfold cappedLogMoment
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      ring

lemma prime_initial_sum (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) (f : ℕ → ℝ) :
    (∑ i ∈ univ.filter (fun i => p i ≤ R), f (p i)) =
      ∑ q ∈ (R + 1).primesBelow, f q := by
  apply sum_bij (fun i hi => p i)
  · intro i hi
    exact WeightedMertens.mem_primes.mpr ⟨hp i, (mem_filter.mp hi).2⟩
  · intro i hi j hj he
    exact hinj he
  · intro q hq
    obtain ⟨hqp, hqR⟩ := WeightedMertens.mem_primes.mp hq
    obtain ⟨i, hi⟩ := hfull q hqp hqR
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, by omega⟩, hi⟩
  · intro i hi
    rfl

lemma cappedLogMoment_split (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) (n : ℕ) :
    cappedLogMoment p (log R) n =
      (∑ q ∈ (R + 1).primesBelow, log (q : ℝ) ^ n / q) +
        log (R : ℝ) ^ n * ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ) := by
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset ι) (fun i => p i ≤ R)
    (fun i => min (log (p i : ℝ)) (log R) ^ n / (p i : ℝ))
  rw [cappedLogMoment, ← hsplit]
  congr 1
  · rw [← prime_initial_sum p hp hinj R hfull (fun q => log (q : ℝ) ^ n / q)]
    apply sum_congr rfl
    intro i hi
    have hh : log (p i : ℝ) ≤ log R := log_le_log (by exact_mod_cast (hp i).pos)
      (by exact_mod_cast (mem_filter.mp hi).2)
    rw [min_eq_left hh]
  · simp only [not_le]
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hh : log (R : ℝ) ≤ log (p i : ℝ) := log_le_log (by exact_mod_cast hR)
      (by exact_mod_cast (mem_filter.mp hi).2.le)
    rw [min_eq_right hh]
    ring

noncomputable def cubicEnergyError : ℝ :=
  1 + 5 * (65 / 64) * WeightedMertens.sharpMomentError +
    2 * normalizerOffset 65 * (1 + WeightedMertens.sharpMomentError)

lemma cubicEnergyError_pos : 0 < cubicEnergyError := by
  unfold cubicEnergyError
  have := WeightedMertens.sharpMomentError_pos
  have := normalizerOffset_pos 65
  positivity

/-- The sharp moment coefficients leave a fixed positive cubic main term. -/
theorem prime_soft_energy_cubic_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hL : 1 ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 1 / 64) :
    log (R : ℝ) ^ 3 / 24 - cubicEnergyError * log (R : ℝ) ^ 2 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q *
          softProfile (fun i => log (p i : ℝ)) (log R) Q) := by
  let L := log (R : ℝ)
  let U := cappedLogMoment p L 2
  let V := cappedLogMoment p L 3
  let T := ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)
  let C := normalizerOffset 65
  let e := WeightedMertens.sharpMomentError
  have hC : 0 < C := normalizerOffset_pos 65
  have he : 0 < e := WeightedMertens.sharpMomentError_pos
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hmoment := WeightedMertens.prime_second_third_log_moments R hR
  have hU : U ≤ L ^ 2 / 2 + 2 * e * L + L ^ 2 * T := by
    dsimp [U]
    rw [cappedLogMoment_split p hp hinj R hR hfull 2]
    have hh := (abs_le.mp hmoment.1).2
    change _ ≤ _ at hh
    dsimp [e, L, T]
    linarith
  have hV : L ^ 3 / 3 - 4 * e * L ^ 2 + L ^ 3 * T ≤ V := by
    dsimp [V]
    rw [cappedLogMoment_split p hp hinj R hR hfull 3]
    have hh := (abs_le.mp hmoment.2).1
    dsimp [e, L, T]
    linarith
  have hnorm := prime_soft_square_lower p hp hinj R hR hfull
  have hdir := prime_soft_dirichlet_le p hp hinj L hL0
  have hbase : L ^ 3 / 3 - L ^ 2 -
      (((65 / 64) * L + C) * U - (2 / 3) * (65 / 64) * V) ≤
        kernelEnergy (fun i => 1 / (p i : ℝ))
          (fun Q => weight (fun i => 1 / (p i : ℝ)) Q *
            softProfile (fun i => log (p i : ℝ)) L Q) := by
    rw [kernelEnergy_weighted _ (prime_marginals p hp)]
    dsimp only [U, V, C] at *
    change L ^ 3 / 3 - L ^ 2 ≤ _ at hnorm
    nlinarith only [hnorm, hdir]
  apply le_trans ?_ hbase
  change L ^ 3 / 24 - cubicEnergyError * L ^ 2 ≤ _
  have hU' := mul_le_mul_of_nonneg_left hU
    (show 0 ≤ (65 / 64 : ℝ) * L + C by positivity)
  have hV' := mul_le_mul_of_nonneg_left hV
    (show 0 ≤ (2 / 3 : ℝ) * (65 / 64) by norm_num)
  have hT' := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ ((65 / 64 : ℝ) / 3) * L ^ 3 + C * L ^ 2 by positivity)
  change (((65 / 64 : ℝ) / 3) * L ^ 3 + C * L ^ 2) * T ≤ _ at hT'
  have hCE := mul_le_mul_of_nonneg_left
    (show L ≤ L ^ 2 by change 1 ≤ L at hL; nlinarith)
    (show 0 ≤ 2 * C * e by positivity)
  have heL : 0 ≤ e * L ^ 2 := by positivity
  have hCL : 0 ≤ C * L ^ 2 := by positivity
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hD : cubicEnergyError = 1 + 5 * (65 / 64) * e + 2 * C * (1 + e) := rfl
  rw [hD]
  nlinarith only [hU', hV', hT', hCE, heL, hCL, hL3]

/-- A sufficiently large logarithmic cutoff gives energy at least log(R)^3/48. -/
theorem prime_soft_energy_cubic (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hL : 1 ≤ log (R : ℝ)) (hlarge : 48 * cubicEnergyError ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 1 / 64) :
    log (R : ℝ) ^ 3 / 48 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q *
          softProfile (fun i => log (p i : ℝ)) (log R) Q) := by
  have hh := prime_soft_energy_cubic_lower p hp hinj R hR hfull hL htail
  have he := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (log (R : ℝ)))
  nlinarith only [hh, he]

#print axioms prime_soft_dirichlet_le
#print axioms cappedLogMoment_split
#print axioms prime_soft_energy_cubic
end Erdos970.FiniteSelberg
