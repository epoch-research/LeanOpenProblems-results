import FormalConjecturesUtil

/-! The interval-count inequalities alone do not imply the extremal-series criterion.
This is an analytic countermodel, not a progression-free set or a disproof of Erdős 3. -/

namespace Erdos3StructuralCountCheck

open Filter
open scoped Topology

noncomputable def weight (n : ℕ) : ℝ :=
  1 / ((Nat.log 4 (n + 1) : ℝ) + 1)

noncomputable def mass (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, weight i

noncomputable def count (N : ℕ) : ℕ := ⌈mass N⌉₊

lemma weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity

lemma weight_le_one (n : ℕ) : weight n ≤ 1 := by
  unfold weight
  apply (div_le_one (by positivity)).mpr
  have := Nat.cast_nonneg (α := ℝ) (Nat.log 4 (n + 1))
  linarith

lemma weight_antitone : Antitone weight := by
  intro m n hmn
  unfold weight
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hmn 1)) 1

lemma weight_tendsto_zero : Tendsto weight atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 4 (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    refine eventually_atTop.mpr ⟨4 ^ k, fun n hn ↦ ?_⟩
    have h := Nat.log_mono_right (b := 4) (hn.trans (Nat.le_succ n))
    simpa only [Nat.log_pow (by norm_num : 1 < 4)] using h
  exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hlog

lemma mass_nonneg (N : ℕ) : 0 ≤ mass N :=
  Finset.sum_nonneg (fun i _ ↦ (weight_pos i).le)

lemma mass_le (N : ℕ) : mass N ≤ N := by
  calc
    _ ≤ ∑ _ ∈ Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ ↦ weight_le_one i)
    _ = N := by simp

lemma mass_monotone : Monotone mass := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun i _ _ ↦ (weight_pos i).le)

lemma mass_add_le (m n : ℕ) : mass (m + n) ≤ mass m + mass n := by
  unfold mass
  rw [Finset.sum_range_add]
  exact add_le_add le_rfl
    (Finset.sum_le_sum (fun i _ ↦ weight_antitone (Nat.le_add_left i m)))

lemma count_zero : count 0 = 0 := by simp [count, mass]

lemma count_monotone : Monotone count := Nat.ceil_mono.comp mass_monotone

lemma count_le (N : ℕ) : count N ≤ N := Nat.ceil_le.mpr (mass_le N)

lemma count_add_le (m n : ℕ) : count (m + n) ≤ count m + count n :=
  (Nat.ceil_mono (mass_add_le m n)).trans (Nat.ceil_add_le _ _)

lemma count_mul_le (m n : ℕ) : count (m * n) ≤ m * count n := by
  induction m with
  | zero => simp [count_zero]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (count_add_le _ _).trans (Nat.add_le_add_right ih _)

lemma count_succ_le (N : ℕ) : count (N + 1) ≤ count N + 1 :=
  (count_add_le N 1).trans (Nat.add_le_add_left (count_le 1) _)

lemma mass_density_tendsto_zero :
    Tendsto (fun N : ℕ ↦ mass N / N) atTop (𝓝 0) := by
  simpa only [mass, div_eq_mul_inv, mul_comm] using weight_tendsto_zero.cesaro

lemma count_density_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (count N : ℝ) / N) atTop (𝓝 0) := by
  have hbound (N : ℕ) : (count N : ℝ) / N ≤ mass N / N + 1 / N := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact (Nat.ceil_lt_add_one (mass_nonneg N)).le
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity))
    (Eventually.of_forall hbound)
    (by simpa using mass_density_tendsto_zero.add tendsto_one_div_atTop_nhds_zero_nat)

lemma geometric_density_antitone :
    Antitone (fun j : ℕ ↦ (count (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro j
  have hbound := count_mul_le 4 (4 ^ j)
  rw [pow_succ']
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hc : (count (4 * 4 ^ j) : ℝ) ≤ 4 * (count (4 ^ j) : ℝ) := by
    exact_mod_cast hbound
  nlinarith [mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ 4 ^ j by positivity)]

lemma geometric_density_lower (j : ℕ) :
    1 / ((j : ℝ) + 1) ≤ (count (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ) := by
  have hmass : ((4 ^ j : ℕ) : ℝ) * (1 / ((j : ℝ) + 1)) ≤ mass (4 ^ j) := by
    calc
      _ = ∑ _ ∈ Finset.range (4 ^ j), (1 / ((j : ℝ) + 1)) := by simp
      _ ≤ mass (4 ^ j) := by
        apply Finset.sum_le_sum
        intro i hi
        unfold weight
        apply one_div_le_one_div_of_le (by positivity)
        have h := Nat.log_mono_right (b := 4) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
        rw [Nat.log_pow (by norm_num : 1 < 4)] at h
        exact_mod_cast Nat.add_le_add_right h 1
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = ((4 ^ j : ℕ) : ℝ) * (1 / ((j : ℝ) + 1)) := mul_comm _ _
    _ ≤ mass (4 ^ j) := hmass
    _ ≤ (count (4 ^ j) : ℝ) := Nat.le_ceil _

lemma geometric_density_not_summable :
    ¬ Summable (fun j : ℕ ↦ (count (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)) := by
  intro hs
  have hh : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) :=
    hs.of_nonneg_of_le (fun j ↦ by positivity) geometric_density_lower
  have hh' : Summable (fun j : ℕ ↦ 1 / ((j + 1 : ℕ) : ℝ)) := by simpa using hh
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hh')

/-- Even natural-valued, monotone, subadditive counts with increments at most one,
vanishing density, and all linear tiling bounds can have a divergent extremal-style series. -/
theorem structural_count_properties_do_not_force_summability :
    ∃ r : ℕ → ℕ,
      r 0 = 0 ∧ Monotone r ∧ (∀ N, r N ≤ N) ∧
      (∀ m n, r (m + n) ≤ r m + r n) ∧
      (∀ m n, r (m * n) ≤ m * r n) ∧
      (∀ N, r (N + 1) ≤ r N + 1) ∧
      Tendsto (fun N : ℕ ↦ (r N : ℝ) / N) atTop (𝓝 0) ∧
      Antitone (fun j : ℕ ↦ (r (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)) ∧
      ¬ Summable (fun j : ℕ ↦ (r (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)) := by
  exact ⟨count, count_zero, count_monotone, count_le, count_add_le,
    count_mul_le, count_succ_le, count_density_tendsto_zero,
    geometric_density_antitone, geometric_density_not_summable⟩

#print axioms structural_count_properties_do_not_force_summability

end Erdos3StructuralCountCheck
