import Submission.BlockMomentError

/-!
The exact all-moment tolerance threshold of a prime-block synthetic model.
The formula uses the least prime in each block. It is not an assertion that
this threshold reaches quadratic mass, or that such models are interval covers.
-/
namespace Erdos970.PrimeBlockMomentError
open Finset Erdos970.BlockMomentObstruction
variable {β : Type*} [Fintype β] [DecidableEq β]

noncomputable def blockDensity (P : β → Finset ℕ) (j : β) : ℝ :=
  ∏ p ∈ P j, (1 - 1 / (p : ℝ))

noncomputable def marginals (P : β → Finset ℕ) (j : β) (p : P j) : ℝ :=
  1 / (p.val : ℝ)

lemma marginals_bounds (P : β → Finset ℕ) (hP : ∀ j, ∀ p ∈ P j, p.Prime) :
    ∀ j p, 0 ≤ marginals P j p ∧ marginals P j p ≤ 1 := by
  intro j p
  have hp := hP j p.val p.property
  have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
  exact ⟨div_nonneg (by norm_num) hp0.le,
    (div_le_one hp0).mpr (by exact_mod_cast hp.one_le)⟩

lemma density_eq (P : β → Finset ℕ) (j : β) :
    (∏ p : P j, (1 - marginals P j p)) = blockDensity P j := by
  exact prod_coe_sort (P j) (fun p => 1 - 1 / (p : ℝ))

lemma odds_eq (P : β → Finset ℕ) (j : β) :
    emptyOdds (marginals P) j = blockDensity P j / (1 - blockDensity P j) := by
  simp only [emptyOdds, density_eq]

/-- Among all intersections, selecting the least prime of each block attains
  the largest absolute moment error. Consequently the tolerance budget below
  is exact for the specified synthetic model. -/
theorem all_moments_unit_iff (P : β → Finset ℕ)
    (hP : ∀ j, ∀ p ∈ P j, p.Prime) (hnon : ∀ j, (P j).Nonempty)
    (hless : ∀ j, blockDensity P j < 1) (X : ℝ) (hX : 0 ≤ X) :
    (∀ T : (j : β) → Finset (P j),
      |(∑ v, X * model (marginals P) v * test T v) -
        X * (∏ j, ∏ p ∈ T j, 1 / (p.val : ℝ))| ≤ 1) ↔
      X * (∏ j, (blockDensity P j / (1 - blockDensity P j)) /
        ((P j).min' (hnon j) : ℝ)) ≤ 1 := by
  let i₀ : (j : β) → P j := fun j => ⟨(P j).min' (hnon j), (P j).min'_mem (hnon j)⟩
  have hm : ∀ j p, marginals P j p ≤ marginals P j (i₀ j) := by
    intro j p
    apply one_div_le_one_div_of_le
    · have hp := hP j _ ((P j).min'_mem (hnon j))
      exact_mod_cast hp.pos
    · exact_mod_cast (P j).min'_le p.val p.property
  have hl : ∀ j, (∏ p : P j, (1 - marginals P j p)) < 1 := by
    simpa only [density_eq] using hless
  have hh := scaled_all_moments_iff (marginals P) (marginals_bounds P hP)
    hl i₀ hm X hX
  simpa only [odds_eq, marginals, i₀, mul_one_div] using hh

/-- Under the explicit budget, these are nonnegative populations of mass X
  with no empty pattern and unit errors in every intersection moment. Prime
  blocks may additionally be chosen disjoint; no such population is asserted
  to be realized by consecutive integers. -/
theorem certificate [Nonempty β] (P : β → Finset ℕ)
    (hP : ∀ j, ∀ p ∈ P j, p.Prime) (hnon : ∀ j, (P j).Nonempty)
    (hhalf : ∀ j, blockDensity P j ≤ 1 / 2) (X : ℝ) (hX : 0 ≤ X)
    (hbudget : X * (∏ j, (blockDensity P j / (1 - blockDensity P j)) /
      ((P j).min' (hnon j) : ℝ)) ≤ 1) :
    (∀ v, 0 ≤ X * model (marginals P) v) ∧
      X * model (marginals P) (fun _ _ => false) = 0 ∧
      (∑ v, X * model (marginals P) v) = X ∧
      ∀ T : (j : β) → Finset (P j),
        |(∑ v, X * model (marginals P) v * test T v) -
          X * (∏ j, ∏ p ∈ T j, 1 / (p.val : ℝ))| ≤ 1 := by
  have hh : ∀ j, (∏ p : P j, (1 - marginals P j p)) ≤ 1 / 2 := by
    simpa only [density_eq] using hhalf
  refine ⟨fun v => mul_nonneg hX (model_nonneg _ (marginals_bounds P hP) hh v),
    by simp [model_empty], ?_, ?_⟩
  · rw [← mul_sum, model_sum _ hh, mul_one]
  · exact (all_moments_unit_iff P hP hnon
      (fun j => lt_of_le_of_lt (hhalf j) (by norm_num)) X hX).mpr hbudget

#print axioms all_moments_unit_iff
#print axioms certificate
end Erdos970.PrimeBlockMomentError
