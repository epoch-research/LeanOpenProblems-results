import Submission.EfficientCover.Cover

/-!
# Elementary efficient CRT composite intervals

For every fixed positive natural `c`, all sufficiently large prime cutoffs `y`
admit a composite interval of length `c*y` whose base has logarithm at most
`(2 + log 4)*y`. This is a large-gap construction only; it makes no assertion
about the original universal finite-limit-point theorem for Erdős Problem 5.
-/

open scoped BigOperators Function

namespace Erdos5EfficientCover

/-- The inclusive prime product is exactly the primorial used by Chebyshev. -/
theorem primorial_eq_prod_primesUpTo (y : ℕ) :
    primorial y = ∏ p ∈ primesUpTo y, p := rfl

/-- CRT combines a covering family into a composite interval, with the base
strictly above `y` and at most `(y+2)*primorial y`. -/
theorem crt_interval_of_cover (c y : ℕ) (hy : 2 ≤ y) (a : ℕ → ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ≤ y → a p < p)
    (hcover : ∀ s : ℕ, 0 < s → s ≤ c * y →
      ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ s % p = a p) :
    ∃ n : ℕ, 2 ≤ n ∧ y < n ∧ n ≤ (y + 2) * primorial y ∧
      ∀ s : ℕ, 0 < s → s ≤ c * y → ¬ Nat.Prime (n + s) := by
  classical
  let r : ℕ → ℕ := fun p => p - a p
  have hnonzero : ∀ p ∈ primesUpTo y, id p ≠ 0 :=
    fun p hp => (mem_primesUpTo.mp hp).1.ne_zero
  have hcoprime : Set.Pairwise (↑(primesUpTo y) : Set ℕ) (Nat.Coprime on id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (mem_primesUpTo.mp hp).1 (mem_primesUpTo.mp hq).1).mpr hpq
  let b := Nat.chineseRemainderOfFinset r id (primesUpTo y) hnonzero hcoprime
  have hblt : (b : ℕ) < primorial y := by
    simpa only [primorial_eq_prod_primesUpTo, id_eq] using
      Nat.chineseRemainderOfFinset_lt_prod r id hnonzero hcoprime
  let n : ℕ := (b : ℕ) + (y + 1) * primorial y
  have hQ : 0 < primorial y := primorial_pos y
  have hyn : y < n := by dsimp [n]; nlinarith
  have hn2 : 2 ≤ n := by omega
  have hnupper : n ≤ (y + 2) * primorial y := by dsimp [n]; nlinarith
  refine ⟨n, hn2, hyn, hnupper, ?_⟩
  intro s hs hsbound hprime
  obtain ⟨p, hpp, hpy, hsclass⟩ := hcover s hs hsbound
  have hpF : p ∈ primesUpTo y := mem_primesUpTo.mpr ⟨hpp, hpy⟩
  have hap : a p < p := ha p hpp hpy
  have hpQ : p ∣ primorial y := by
    rw [primorial_eq_prod_primesUpTo]
    exact Finset.dvd_prod_of_mem (fun p => p) hpF
  have hm0 : Nat.ModEq p ((y + 1) * primorial y) 0 :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hpQ (y + 1))
  have hb : Nat.ModEq p (b : ℕ) (p - a p) := b.property p hpF
  have hnmod : Nat.ModEq p n (p - a p) := by
    simpa only [n, add_zero] using hb.add hm0
  have hsmod : Nat.ModEq p s (a p) := by
    change s % p = a p % p
    rw [Nat.mod_eq_of_lt hap]
    exact hsclass
  have hnsp : Nat.ModEq p (n + s) p := by
    simpa only [Nat.sub_add_cancel hap.le] using hnmod.add hsmod
  have hpdiv : p ∣ n + s := Nat.modEq_zero_iff_dvd.mp
    (hnsp.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)))
  rcases (Nat.dvd_prime hprime).mp hpdiv with hpone | hpeq
  · exact hpp.ne_one hpone
  · omega

/-- Chebyshev's elementary primorial logarithm bound, at a natural cutoff. -/
theorem log_primorial_le (y : ℕ) :
    Real.log (primorial y : ℝ) ≤ Real.log 4 * (y : ℝ) := by
  have h := Chebyshev.theta_le_log4_mul_x (x := (y : ℝ)) (Nat.cast_nonneg y)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  exact h

/-- Every positive base below the CRT construction's bound has the stated log bound. -/
theorem log_le_of_le_primorial_bound (y n : ℕ) (hy : 2 ≤ y) (hn : 0 < n)
    (hbound : n ≤ (y + 2) * primorial y) :
    Real.log (n : ℝ) ≤ (2 + Real.log 4) * (y : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hQpos : (0 : ℝ) < primorial y := by exact_mod_cast primorial_pos y
  have hbound' : (n : ℝ) ≤ ((y : ℝ) + 2) * (primorial y : ℝ) := by exact_mod_cast hbound
  have hlogy : Real.log ((y : ℝ) + 2) ≤ 2 * (y : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (y : ℝ) + 2)
    have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
    linarith
  calc
    Real.log (n : ℝ) ≤ Real.log (((y : ℝ) + 2) * (primorial y : ℝ)) :=
      Real.log_le_log hnpos hbound'
    _ = Real.log ((y : ℝ) + 2) + Real.log (primorial y : ℝ) :=
      Real.log_mul (by positivity) hQpos.ne'
    _ ≤ 2 * (y : ℝ) + Real.log 4 * (y : ℝ) := add_le_add hlogy (log_primorial_le y)
    _ = (2 + Real.log 4) * (y : ℝ) := by ring

/-- A version retaining both the base's primorial bound and its logarithmic bound. -/
theorem efficient_crt_interval (c : ℕ) (hc : 1 ≤ c) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
      ∃ n : ℕ, 2 ≤ n ∧ y < n ∧ n ≤ (y + 2) * primorial y ∧
        Real.log (n : ℝ) ≤ (2 + Real.log 4) * (y : ℝ) ∧
        ∀ s : ℕ, 0 < s → s ≤ c * y → ¬ Nat.Prime (n + s) := by
  obtain ⟨Y, hY⟩ := efficient_cover c hc
  refine ⟨max Y 2, ?_⟩
  intro y hy
  have hyY : Y ≤ y := (le_max_left Y 2).trans hy
  have hy2 : 2 ≤ y := (le_max_right Y 2).trans hy
  obtain ⟨a, ha, hcover⟩ := hY y hyY
  obtain ⟨n, hn2, hyn, hnupper, hncover⟩ := crt_interval_of_cover c y hy2 a ha hcover
  exact ⟨n, hn2, hyn, hnupper,
    log_le_of_le_primorial_bound y n hy2 (by omega) hnupper, hncover⟩

/-- The requested log-controlled composite interval for every fixed positive `c`.
This is not the universal finite-normalized-gap limit-point assertion. -/
theorem logcontrolled_composite_interval (c : ℕ) (hc : 1 ≤ c) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
      ∃ n : ℕ, 2 ≤ n ∧
        Real.log (n : ℝ) ≤ (2 + Real.log 4) * (y : ℝ) ∧
        ∀ s : ℕ, 0 < s → s ≤ c * y → ¬ Nat.Prime (n + s) := by
  obtain ⟨Y, hY⟩ := efficient_crt_interval c hc
  refine ⟨Y, ?_⟩
  intro y hy
  obtain ⟨n, hn2, _, _, hnlog, hncover⟩ := hY y hy
  exact ⟨n, hn2, hnlog, hncover⟩

end Erdos5EfficientCover

#print axioms Erdos5EfficientCover.crt_interval_of_cover
#print axioms Erdos5EfficientCover.log_primorial_le
#print axioms Erdos5EfficientCover.log_le_of_le_primorial_bound
#print axioms Erdos5EfficientCover.efficient_crt_interval
#print axioms Erdos5EfficientCover.logcontrolled_composite_interval
