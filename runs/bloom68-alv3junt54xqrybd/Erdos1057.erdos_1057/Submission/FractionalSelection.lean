import FormalConjecturesUtil

/-!
# Finite fractional-knapsack selection and rounding

For nonnegative real costs and gains on a finite set, a target between zero
and the total gain can be attained by taking some items fully and at most one
item fractionally, at cost at most the target fraction of the total cost.
Rounding that last item up adds at most the maximum individual cost.

The proof is a finite greedy induction, not an invocation of an optimization
result. At each stage it removes an item of least cost per positive gain.
The comparisons are cross-multiplied; zero-gain items are never selected and
zero-cost items cause no division by zero. The only divisions are by strictly
positive gains or total gains. The fractional certificate also covers both
endpoint targets, zero and the total gain.

This is abstract groundwork: it makes no assumptions about logarithms,
prime powers, divisors, or the Carmichael function.
-/

open scoped BigOperators

namespace FractionalSelection

variable {ι : Type*}

/-- There is a positive-gain item whose cost/gain ratio is least, in the
cross-multiplied sense, and hence is at most the aggregate cost/gain ratio.
Zero-gain items are included in the cross-multiplied comparison. -/
theorem exists_min_cost_per_gain (s : Finset ι) (c g : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hG : 0 < ∑ i ∈ s, g i) :
    ∃ i ∈ s, 0 < g i ∧
      (∀ j ∈ s, c i * g j ≤ c j * g i) ∧
      c i * (∑ j ∈ s, g j) ≤ g i * (∑ j ∈ s, c j) := by
  classical
  obtain ⟨k, hks, hgk⟩ := (Finset.sum_pos_iff_of_nonneg hg).mp hG
  have hp : (s.filter fun i => 0 < g i).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨hks, hgk⟩⟩
  obtain ⟨i, hip, hmin⟩ :=
    Finset.exists_min_image (s.filter fun i => 0 < g i) (fun i => c i / g i) hp
  obtain ⟨his, hgi⟩ := Finset.mem_filter.mp hip
  have hcross : ∀ j ∈ s, c i * g j ≤ c j * g i := by
    intro j hjs
    by_cases hgj : 0 < g j
    · exact (div_le_div_iff₀ hgi hgj).mp
        (hmin j (Finset.mem_filter.mpr ⟨hjs, hgj⟩))
    · have hzero : g j = 0 := le_antisymm (le_of_not_gt hgj) (hg j hjs)
      rw [hzero, mul_zero]
      exact mul_nonneg (hc j hjs) hgi.le
  refine ⟨i, his, hgi, hcross, ?_⟩
  calc
    c i * (∑ j ∈ s, g j) = ∑ j ∈ s, c i * g j := Finset.mul_sum s g (c i)
    _ ≤ ∑ j ∈ s, c j * g i := Finset.sum_le_sum hcross
    _ = (∑ j ∈ s, c j) * g i := (Finset.sum_mul s c (g i)).symm
    _ = g i * (∑ j ∈ s, c j) := mul_comm _ _

/-- Taking a below-average item fully and allocating the residual target at
its residual aggregate ratio stays within the original proportional budget. -/
private theorem residual_budget_le {C G c g U : ℝ}
    (hG : 0 < G) (hrest : 0 < G - g)
    (havg : c * G ≤ g * C) (hUG : U ≤ G) :
    c + (U - g) / (G - g) * (C - c) ≤ U / G * C := by
  have hprod : 0 ≤ (G - U) * (g * C - c * G) :=
    mul_nonneg (sub_nonneg.mpr hUG) (sub_nonneg.mpr havg)
  calc
    c + (U - g) / (G - g) * (C - c) =
        (c * (G - g) + (U - g) * (C - c)) / (G - g) := by
      field_simp
    _ ≤ (U * C) / G := (div_le_div_iff₀ hrest hG).mpr (by nlinarith [hprod])
    _ = U / G * C := by ring

/-- A fractional selection with at most one fractional item. The full-item
set `T` is a proper subset of `s`: the positive-gain pivot `j` belongs to `s`
but not to `T`. Its coefficient `θ` is in `[0,1]`, the gain is exactly `U`,
and its cost is at most `(U / totalGain) * totalCost`.

Repeated least-ratio deletion implements the greedy ordering without needing
a tie-breaking order on the index type. -/
theorem exists_fractional_selection (s : Finset ι) (c g : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hG : 0 < ∑ i ∈ s, g i) {U : ℝ}
    (hU : 0 ≤ U) (hUG : U ≤ ∑ i ∈ s, g i) :
    ∃ T : Finset ι, T ⊆ s ∧
      ∃ j ∈ s, j ∉ T ∧ 0 < g j ∧
        ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
          (∑ i ∈ T, g i) + θ * g j = U ∧
          (∑ i ∈ T, c i) + θ * c j ≤
            U / (∑ i ∈ s, g i) * (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.eraseInduction generalizing U with
  | H s ih =>
    obtain ⟨i, his, hgi, _, havg⟩ := exists_min_cost_per_gain s c g hc hg hG
    by_cases hUi : U ≤ g i
    · have hratio : c i / g i ≤ (∑ j ∈ s, c j) / (∑ j ∈ s, g j) :=
        (div_le_div_iff₀ hgi hG).mpr (by simpa only [mul_comm] using havg)
      refine ⟨∅, Finset.empty_subset s, i, his, by simp, hgi,
        U / g i, div_nonneg hU hgi.le, (div_le_one hgi).mpr hUi, ?_, ?_⟩
      · simp only [Finset.sum_empty, zero_add, div_mul_cancel₀ U hgi.ne']
      · simp only [Finset.sum_empty, zero_add]
        calc
          U / g i * c i = U * (c i / g i) := by ring
          _ ≤ U * ((∑ j ∈ s, c j) / (∑ j ∈ s, g j)) :=
            mul_le_mul_of_nonneg_left hratio hU
          _ = U / (∑ j ∈ s, g j) * (∑ j ∈ s, c j) := by ring
    · have hiU : g i < U := lt_of_not_ge hUi
      have hgsplit := Finset.sum_erase_add s g his
      have hcsplit := Finset.sum_erase_add s c his
      have hGrest : 0 < ∑ j ∈ s.erase i, g j := by linarith
      have hUrest : 0 ≤ U - g i := by linarith
      have hUrestG : U - g i ≤ ∑ j ∈ s.erase i, g j := by linarith
      obtain ⟨T, hT, j, hjs, hjT, hgj, θ, hθ0, hθ1, hgain, hcost⟩ :=
        ih i his (fun k hk => hc k (Finset.mem_of_mem_erase hk))
          (fun k hk => hg k (Finset.mem_of_mem_erase hk)) hGrest hUrest hUrestG
      have hiT : i ∉ T := fun hi => Finset.notMem_erase i s (hT hi)
      have hjinsert : j ∉ insert i T := by
        intro hj
        rcases Finset.mem_insert.mp hj with hji | hjT'
        · exact (Finset.mem_erase.mp hjs).1 hji
        · exact hjT hjT'
      have hbudget : c i + (U - g i) / (∑ k ∈ s.erase i, g k) *
          (∑ k ∈ s.erase i, c k) ≤
          U / (∑ k ∈ s, g k) * (∑ k ∈ s, c k) := by
        have hgrest : (∑ k ∈ s.erase i, g k) = (∑ k ∈ s, g k) - g i := by
          linarith
        have hcrest : (∑ k ∈ s.erase i, c k) = (∑ k ∈ s, c k) - c i := by
          linarith
        rw [hgrest, hcrest]
        exact residual_budget_le hG (by linarith) havg hUG
      refine ⟨insert i T, Finset.insert_subset his (hT.trans (Finset.erase_subset i s)),
        j, Finset.mem_of_mem_erase hjs, hjinsert, hgj, θ, hθ0, hθ1, ?_, ?_⟩
      · rw [Finset.sum_insert hiT]
        linarith
      · rw [Finset.sum_insert hiT]
        linarith

/-- Fractional-knapsack rounding on an arbitrary finite set. If every cost
is at most `M`, there is a subset with gain at least the target and cost at
most the target fraction of the total cost, plus `M`.

No positivity of individual costs or gains, and no separate nonnegativity
assumption on `M`, is required. -/
theorem exists_subset (s : Finset ι) (c g : ι → ℝ) (M U : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hG : 0 < ∑ i ∈ s, g i) (hcM : ∀ i ∈ s, c i ≤ M)
    (hU : 0 ≤ U) (hUG : U ≤ ∑ i ∈ s, g i) :
    ∃ T : Finset ι, T ⊆ s ∧ U ≤ ∑ i ∈ T, g i ∧
      (∑ i ∈ T, c i) ≤ U / (∑ i ∈ s, g i) * (∑ i ∈ s, c i) + M := by
  classical
  obtain ⟨T, hT, j, hjs, hjT, hgj, θ, hθ0, hθ1, hgain, hcost⟩ :=
    exists_fractional_selection s c g hc hg hG hU hUG
  refine ⟨insert j T, Finset.insert_subset hjs hT, ?_, ?_⟩
  · rw [Finset.sum_insert hjT]
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) hgj.le]
  · rw [Finset.sum_insert hjT]
    nlinarith [mul_nonneg hθ0 (hc j hjs), hcM j hjs]

/-- The same rounding bound with named total cost `C` and total gain `G`. -/
theorem exists_subset_of_totals (s : Finset ι) (c g : ι → ℝ) (C G M U : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hC : ∑ i ∈ s, c i = C) (hGsum : ∑ i ∈ s, g i = G)
    (hG : 0 < G) (hcM : ∀ i ∈ s, c i ≤ M)
    (hU : 0 ≤ U) (hUG : U ≤ G) :
    ∃ T : Finset ι, T ⊆ s ∧ U ≤ ∑ i ∈ T, g i ∧
      (∑ i ∈ T, c i) ≤ (U / G) * C + M := by
  simpa only [hC, hGsum] using
    exists_subset s c g M U hc hg (by simpa only [hGsum] using hG) hcM hU
      (by simpa only [hGsum] using hUG)

/-- A `Fintype` version, selecting a finite subset of all indices. -/
theorem exists_finset [Fintype ι] (c g : ι → ℝ) (M U : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hg : ∀ i, 0 ≤ g i)
    (hG : 0 < ∑ i, g i) (hcM : ∀ i, c i ≤ M)
    (hU : 0 ≤ U) (hUG : U ≤ ∑ i, g i) :
    ∃ T : Finset ι, U ≤ ∑ i ∈ T, g i ∧
      (∑ i ∈ T, c i) ≤ U / (∑ i, g i) * (∑ i, c i) + M := by
  classical
  obtain ⟨T, _, hgain, hcost⟩ := exists_subset Finset.univ c g M U
    (fun i _ => hc i) (fun i _ => hg i) hG (fun i _ => hcM i) hU hUG
  exact ⟨T, hgain, hcost⟩

end FractionalSelection
