import Submission.BrunCriterion

/-!
Explicit reciprocal-prime estimates for the truncated sieve. Chebyshev's theta
bound controls each dyadic block, reducing the necessary truncation order.
-/
namespace Erdos970.BrunCriterion

noncomputable def dyadicPrimes (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime

/-- Each dyadic block contributes at most `4/j` to the sum of prime reciprocals. -/
theorem dyadic_reciprocal_sum_le (j : ℕ) (hj : 0 < j) :
    (∑ p ∈ dyadicPrimes j, (1 : ℝ) / p) ≤ 4 / (j : ℝ) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowpos : 0 < (2 : ℝ) ^ j := by positivity
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogs : ((dyadicPrimes j).card : ℝ) * (j * Real.log 2) ≤
      Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
    calc
      _ = ∑ p ∈ dyadicPrimes j, (j : ℝ) * Real.log 2 := by simp
      _ ≤ ∑ p ∈ dyadicPrimes j, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hplo := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
        have hh := Real.log_le_log hpowpos (show (2 : ℝ) ^ j ≤ p by exact_mod_cast hplo)
        simpa only [Real.log_pow] using hh
      _ ≤ Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
        simp only [Chebyshev.theta, Nat.floor_natCast]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
          obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hpI
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpp.pos, hhi.le⟩, hpp⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  have htheta : Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) ≤ 4 * Real.log 2 * (2 : ℝ) ^ j := by
    calc
      _ ≤ Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) := Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = _ := by rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]; ring
  have hcard : ((dyadicPrimes j).card : ℝ) * j ≤ 4 * (2 : ℝ) ^ j := by
    apply (mul_le_mul_iff_left₀ hlog2).mp
    nlinarith only [hlogs, htheta]
  calc
    (∑ p ∈ dyadicPrimes j, (1 : ℝ) / p) ≤ ∑ p ∈ dyadicPrimes j, 1 / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro p hp
      have hplo := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
      exact one_div_le_one_div_of_le hpowpos (by exact_mod_cast hplo)
    _ = ((dyadicPrimes j).card : ℝ) / (2 : ℝ) ^ j := by simp [div_eq_mul_inv]
    _ ≤ 4 / (j : ℝ) := (div_le_div_iff₀ hpowpos hjR).mpr hcard

/-- A bound uniform over arbitrary sets of at most `k` primes, not just prime prefixes. -/
theorem prime_reciprocal_sum_le (k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPk : P.card ≤ k) :
    (∑ p ∈ P, (1 : ℝ) / p) ≤
      5 + 4 * (Nat.clog 2 (Nat.log 2 (k + 1) + 1) : ℝ) * Real.log 2 := by
  classical
  let L := Nat.log 2 (k + 1) + 1
  let J := Nat.clog 2 L
  let A := P.filter (fun p => p ≤ k)
  let B := P.filter (fun p => ¬p ≤ k)
  have hL : 0 < L := by dsimp [L]; omega
  have hsplit : (∑ p ∈ A, (1 : ℝ) / p) + (∑ p ∈ B, (1 : ℝ) / p) = ∑ p ∈ P, (1 : ℝ) / p :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ k) (fun p => (1 : ℝ) / p)
  have hBcard : B.card ≤ k := (Finset.card_filter_le _ _).trans hPk
  have hlarge : (∑ p ∈ B, (1 : ℝ) / p) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ B, 1 / ((k : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpk : k + 1 ≤ p := by have := (Finset.mem_filter.mp hp).2; omega
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpk)
      _ = (B.card : ℝ) / ((k : ℝ) + 1) := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
        (by exact_mod_cast hBcard.trans (Nat.le_succ k))
  have hmap : ∀ p ∈ A, Nat.log 2 p ∈ Finset.Icc 1 L := by
    intro p hp
    obtain ⟨hpP, hpk⟩ := Finset.mem_filter.mp hp
    have hpprime := hP p hpP
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.le_log_of_pow_le (by decide) (by simpa using hpprime.two_le)
    · have hh : Nat.log 2 p ≤ Nat.log 2 (k + 1) :=
        Nat.log_mono_right (show p ≤ k + 1 by omega)
      dsimp [L]
      omega
  have hsmall : (∑ p ∈ A, (1 : ℝ) / p) ≤ 4 * (1 + Real.log (L : ℝ)) := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 L, ∑ p ∈ A.filter (fun p => Nat.log 2 p = j), (1 : ℝ) / p :=
        (Finset.sum_fiberwise_of_maps_to hmap _).symm
      _ ≤ ∑ j ∈ Finset.Icc 1 L, ∑ p ∈ dyadicPrimes j, (1 : ℝ) / p := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpA, hlog⟩ := Finset.mem_filter.mp hp
          have hpprime := hP p (Finset.mem_filter.mp hpA).1
          have hjpos : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
          have hb := (Nat.log_eq_iff (Or.inl hjpos.ne')).mp hlog
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hb, hpprime⟩
        · intro p hp _
          positivity
      _ ≤ ∑ j ∈ Finset.Icc 1 L, 4 / (j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact dyadic_reciprocal_sum_le j (by have := (Finset.mem_Icc.mp hj).1; omega)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by norm_num : (0 : ℝ) ≤ 4)
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          Finset.mul_sum, div_eq_mul_inv] using hh
  have hlog : Real.log (L : ℝ) ≤ (J : ℝ) * Real.log 2 := by
    have hLpow : L ≤ 2 ^ J := Nat.le_pow_clog (by decide) L
    have hh := Real.log_le_log (by exact_mod_cast hL) (show (L : ℝ) ≤ (2 : ℝ) ^ J by exact_mod_cast hLpow)
    simpa only [Real.log_pow] using hh
  change _ ≤ 5 + 4 * (J : ℝ) * Real.log 2
  linarith

#print axioms prime_reciprocal_sum_le
end Erdos970.BrunCriterion
