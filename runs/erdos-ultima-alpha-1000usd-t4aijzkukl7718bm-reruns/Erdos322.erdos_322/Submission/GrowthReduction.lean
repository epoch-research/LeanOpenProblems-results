import FormalConjecturesUtil

/-! Growth conditions relevant to the conjecture. -/

namespace Erdos322Research

open Filter

/-- Having no polynomially large peaks is exactly eventual domination by every
positive power. This holds for an arbitrary real-valued sequence. -/
theorem no_polynomial_peaks_iff (r : ℕ → ℝ) :
    (¬ ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < r n}.Infinite) ↔
      ∀ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, r n ≤ (n : ℝ) ^ c := by
  constructor
  · intro h c hc
    have hf : {n : ℕ | (n : ℝ) ^ c < r n}.Finite := by
      by_contra hi
      exact h ⟨c, hc, hi⟩
    obtain ⟨N, hN⟩ := hf.bddAbove
    filter_upwards [eventually_gt_atTop N] with n hn
    by_contra hr
    have hmem : n ∈ {n : ℕ | (n : ℝ) ^ c < r n} := not_le.mp hr
    have := hN hmem
    omega
  · intro h ⟨c, hc, hinf⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h c hc)
    have hs : {n : ℕ | (n : ℝ) ^ c < r n} ⊆ Set.Iio N := by
      intro n hn
      by_contra hnot
      have hge : N ≤ n := Nat.le_of_not_gt hnot
      exact (not_lt_of_ge (hN n hge)) hn
    exact hinf (Set.Finite.subset (Set.finite_Iio N) hs)


/-- The usual uniform `O(n^ε)` condition is equivalent to the absence of
polynomially large peaks. -/
theorem no_polynomial_peaks_iff_uniform_bound (r : ℕ → ℕ) :
    (¬ ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < (r n : ℝ)}.Infinite) ↔
      ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
        ∀ n : ℕ, 1 ≤ n → (r n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  rw [no_polynomial_peaks_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
    let S : ℝ := ∑ i ∈ Finset.range N, (r i : ℝ)
    have hS : 0 ≤ S := by dsimp [S]; positivity
    refine ⟨1 + S, by positivity, ?_⟩
    intro n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hnreal hε.le
    by_cases hsmall : n < N
    · have hrs : (r n : ℝ) ≤ S := by
        exact Finset.single_le_sum (f := fun i : ℕ ↦ (r i : ℝ))
          (fun _ _ ↦ Nat.cast_nonneg _) (Finset.mem_range.mpr hsmall)
      calc
        (r n : ℝ) ≤ 1 + S := by linarith
        _ = (1 + S) * 1 := by ring
        _ ≤ (1 + S) * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hp (by positivity)
    · calc
        (r n : ℝ) ≤ (n : ℝ) ^ ε := hN n (by omega)
        _ = 1 * (n : ℝ) ^ ε := by ring
        _ ≤ (1 + S) * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · intro h c hc
    have hh : 0 < c / 2 := by linarith
    obtain ⟨C, hCpos, hC⟩ := h (c / 2) hh
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (c / 2)) atTop atTop :=
      (tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop (1 : ℕ)] with n hpow hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      (r n : ℝ) ≤ C * (n : ℝ) ^ (c / 2) := hC n hn
      _ ≤ (n : ℝ) ^ (c / 2) * (n : ℝ) ^ (c / 2) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (n : ℝ) ^ c := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring

end Erdos322Research
