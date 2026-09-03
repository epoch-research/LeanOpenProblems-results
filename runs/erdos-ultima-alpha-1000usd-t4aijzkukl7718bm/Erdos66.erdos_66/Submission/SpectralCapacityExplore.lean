import Submission.DyadicPrefixEnergyExplore

/-! A conditional critical-scale capacity test expressed entirely through
finite block masses.  No Fourier representation, measure construction, or
hypothesis of this test is inferred from the Erdős 66 conjecture here. -/
namespace Erdos66SpectralCapacity
open Filter Erdos66DyadicPrefixEnergy
open scoped Topology Classical

lemma normalized_prefix_floor (M q S C t : ℝ)
    (hM : 0 < M) (hC : 0 < C) (ht : 0 < t)
    (huncertainty : M ≤ q * S) (hcap : q ^ 2 ≤ C * M * t) :
    (1 / C) / t ≤ S ^ 2 / M := by
  have hsq := pow_le_pow_left₀ hM.le huncertainty 2
  have hupper := mul_le_mul_of_nonneg_right hcap (sq_nonneg S)
  have hprod : M * M ≤ (C * t * S ^ 2) * M := by
    nlinarith [show (q * S) ^ 2 = q ^ 2 * S ^ 2 by ring]
  have hl : M ≤ C * t * S ^ 2 := (mul_le_mul_iff_left₀ hM).mp hprod
  rw [div_div]
  exact (div_le_div_iff₀ (mul_pos hC ht) hM).mpr (by nlinarith only [hl])

lemma finite_scaled_prefix_energy (y E : ℕ → ℝ) (L : ℕ)
    (hblock : ∀ n < L, y n ^ 2 ≤ (4 : ℝ) ^ n * E n) :
    (∑ n ∈ Finset.range L,
      (∑ j ∈ Finset.range (n + 1), y j) ^ 2 / (4 : ℝ) ^ n) ≤
        4 * ∑ n ∈ Finset.range L, E n := by
  have hp (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hh := finite_energy (fun j ↦ y j / (2 : ℝ) ^ j) L
  simp only [running_eq_scaled_prefix, div_pow, hp] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro n hn
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)).mpr
    (by simpa only [mul_comm] using hblock n (Finset.mem_range.mp hn))

/-- If critical support-size and uncertainty budgets hold at every scale up
to L, the total block energy must pay a harmonic sum in L. -/
theorem finite_critical_capacity_budget (y E q : ℕ → ℝ) (L : ℕ)
    (C : ℝ) (hC : 0 < C)
    (hblock : ∀ n < L, y n ^ 2 ≤ (4 : ℝ) ^ n * E n)
    (huncertainty : ∀ n < L,
      (4 : ℝ) ^ n ≤ q n * (∑ j ∈ Finset.range (n + 1), y j))
    (hcap : ∀ n < L, q n ^ 2 ≤ C * (4 : ℝ) ^ n * ((n : ℝ) + 1)) :
    (∑ n ∈ Finset.range L, (1 / C) / ((n : ℝ) + 1)) ≤
      4 * ∑ n ∈ Finset.range L, E n := by
  apply le_trans _ (finite_scaled_prefix_energy y E L hblock)
  apply Finset.sum_le_sum
  intro n hn
  exact normalized_prefix_floor _ _ _ _ _ (by positivity) hC (by positivity)
    (huncertainty n (Finset.mem_range.mp hn)) (hcap n (Finset.mem_range.mp hn))

/-- With finite total block energy, a critical support bound cannot hold on
an entire tail. Every constant is exceeded at arbitrarily late scales. -/
theorem critical_capacity_unbounded (y E q : ℕ → ℝ)
    (hE : Summable E)
    (hblock : ∀ n, y n ^ 2 ≤ (4 : ℝ) ^ n * E n)
    (huncertainty : ∀ᶠ n : ℕ in atTop,
      (4 : ℝ) ^ n ≤ q n * (∑ j ∈ Finset.range (n + 1), y j))
    (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∃ n ≥ N, C * (4 : ℝ) ^ n * ((n : ℝ) + 1) < q n ^ 2 := by
  by_contra hh
  push_neg at hh
  apply no_eventual_harmonic_floor y E hE hblock (1 / C) (by positivity)
  filter_upwards [huncertainty, eventually_ge_atTop N] with n hn hN
  exact normalized_prefix_floor _ _ _ _ _ (by positivity) hC (by positivity)
    hn (hh n hN)

end Erdos66SpectralCapacity
