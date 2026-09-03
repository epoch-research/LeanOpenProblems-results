import Submission.SpectralCapacityExplore

/-! The conditional capacity test instantiated with one actual fourth-power
summable coefficient sequence.  This does not identify such a sequence for
an Erdős 66 witness. -/
namespace Erdos66QuarticPrefixCapacity
open Filter Erdos66DyadicPrefixEnergy Erdos66SpectralCapacity
open scoped Topology Classical

noncomputable def block : ℕ → Finset ℕ
  | 0 => Finset.range 1
  | n + 1 => Finset.Ico (4 ^ n) (4 ^ (n + 1))

lemma block_card_le (n : ℕ) : (block n).card ≤ 4 ^ n := by
  cases n with
  | zero => simp [block]
  | succ n =>
      simp only [block, Nat.card_Ico]
      exact Nat.sub_le _ _

lemma block_sum_prefix (g : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ∑ i ∈ block j, g i) =
      ∑ i ∈ Finset.range (4 ^ n), g i := by
  induction n with
  | zero => simp [block]
  | succ n ih =>
      rw [Finset.sum_range_succ (f := fun j ↦ ∑ i ∈ block j, g i) (n + 1), ih,
        block]
      exact Finset.sum_range_add_sum_Ico g (Nat.pow_le_pow_right (by decide) (by omega))

lemma block_square_mass_le (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ block n, x i ^ 2) ^ 2 ≤
      (4 : ℝ) ^ n * (∑ i ∈ block n, x i ^ 4) := by
  have hc : ((block n).card : ℝ) ≤ (4 : ℝ) ^ n := by
    exact_mod_cast block_card_le n
  have hh := sq_sum_le_card_mul_sum_sq (s := block n) (f := fun i ↦ x i ^ 2)
  have he (i : ℕ) : (x i ^ 2) ^ 2 = x i ^ 4 := by ring
  simp only [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hc
    (Finset.sum_nonneg (fun i hi ↦ by positivity)))

lemma summable_block_fourth (x : ℕ → ℝ)
    (hx : Summable (fun i ↦ x i ^ 4)) :
    Summable (fun n ↦ ∑ i ∈ block n, x i ^ 4) := by
  apply summable_of_sum_range_le
    (fun n ↦ Finset.sum_nonneg (fun i hi ↦ by positivity))
    (c := ∑' i, x i ^ 4)
  intro L
  cases L with
  | zero => simp only [Finset.sum_range_zero]; exact tsum_nonneg (fun i ↦ by positivity)
  | succ n =>
      rw [block_sum_prefix]
      exact hx.sum_le_tsum _ (fun i hi ↦ by positivity)

/-- A geometric-scale Hardy estimate for fourth-power summable sequences. -/
theorem summable_geometric_prefix_energy (x : ℕ → ℝ)
    (hx : Summable (fun i ↦ x i ^ 4)) :
    Summable (fun n ↦
      (∑ i ∈ Finset.range (4 ^ n), x i ^ 2) ^ 2 / (4 : ℝ) ^ n) := by
  have hh := summable_scaled_prefix_sq
    (fun n ↦ ∑ i ∈ block n, x i ^ 2)
    (fun n ↦ ∑ i ∈ block n, x i ^ 4)
    (summable_block_fourth x hx) (block_square_mass_le x)
  simpa only [block_sum_prefix] using hh

/-- The normalized square-prefix mass has no positive harmonic lower floor
on an entire tail. In particular it becomes arbitrarily small after the
additional factor n+1, along arbitrarily late geometric scales. -/
theorem frequently_small_geometric_prefix (x : ℕ → ℝ)
    (hx : Summable (fun i ↦ x i ^ 4))
    (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n ≥ N, ((n : ℝ) + 1) *
      (∑ i ∈ Finset.range (4 ^ n), x i ^ 2) ^ 2 < c * (4 : ℝ) ^ n := by
  by_contra hh
  push_neg at hh
  apply no_eventual_harmonic_floor
    (fun n ↦ ∑ i ∈ block n, x i ^ 2)
    (fun n ↦ ∑ i ∈ block n, x i ^ 4)
    (summable_block_fourth x hx) (block_square_mass_le x) c hc
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [block_sum_prefix]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)).mpr
  nlinarith only [hh n hn]

/-- If a single fourth-power summable sequence obeys the stated prefix
uncertainty inequality, its capacity sequence exceeds every critical bound
at arbitrarily late scales. -/
theorem consistent_coefficient_capacity (x q : ℕ → ℝ)
    (hx : Summable (fun i ↦ x i ^ 4))
    (huncertainty : ∀ᶠ n : ℕ in atTop,
      (4 : ℝ) ^ n ≤ q n * (∑ i ∈ Finset.range (4 ^ n), x i ^ 2))
    (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∃ n ≥ N, C * (4 : ℝ) ^ n * ((n : ℝ) + 1) < q n ^ 2 := by
  apply critical_capacity_unbounded
    (fun n ↦ ∑ i ∈ block n, x i ^ 2)
    (fun n ↦ ∑ i ∈ block n, x i ^ 4) q
    (summable_block_fourth x hx) (block_square_mass_le x) _ C hC N
  simpa only [block_sum_prefix] using huncertainty

end Erdos66QuarticPrefixCapacity
