import Submission.MongeRearrangement

/-! Doubly stochastic finite Monge couplings. This extends the permutation
inequality, not the increasing-convex-order or covering-family comparison. -/
namespace Erdos7Monge
open scoped BigOperators
open Finset
set_option maxHeartbeats 1000000

/-- The sorted pairing dominates every doubly stochastic coupling of two
co-monotone finite lists, by Birkhoff's convex decomposition. -/
theorem sum_monge_doublyStochastic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (hM : M ∈ doublyStochastic ℚ ι)
    (H : ℚ → ℚ → ℚ)
    (hH : ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
      H x₁ y₂ + H x₂ y₁ ≤ H x₁ y₁ + H x₂ y₂)
    (f g : ι → ℚ) (hfg : MonovaryOn f g (Finset.univ : Finset ι)) :
    (∑ i, ∑ j, M i j * H (f i) (g j)) ≤ ∑ i, H (f i) (g i) := by
  classical
  obtain ⟨w, hw, hws, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hij (i j : ι) : M i j = ∑ σ : Equiv.Perm ι, w σ * (σ.permMatrix ℚ) i j := by
    rw [← hwM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hperm (σ : Equiv.Perm ι) (i : ι) :
      (∑ j, (σ.permMatrix ℚ) i j * H (f i) (g j)) = H (f i) (g (σ i)) := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  calc
    _ = ∑ i, ∑ j, ∑ σ : Equiv.Perm ι, w σ * (σ.permMatrix ℚ) i j * H (f i) (g j) := by
      simp_rw [hij, Finset.sum_mul]
    _ = ∑ i, ∑ σ : Equiv.Perm ι, ∑ j, w σ * (σ.permMatrix ℚ) i j * H (f i) (g j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ σ : Equiv.Perm ι, ∑ i, ∑ j, w σ * (σ.permMatrix ℚ) i j * H (f i) (g j) :=
      Finset.sum_comm
    _ = ∑ σ : Equiv.Perm ι, w σ * ∑ i, H (f i) (g (σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simp_rw [mul_assoc, ← Finset.mul_sum, hperm]
    _ ≤ ∑ σ : Equiv.Perm ι, w σ * ∑ i, H (f i) (g i) := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (hw σ)
      exact sum_monge_comp_perm_le Finset.univ H hH f g σ hfg (by simp)
    _ = _ := by rw [← Finset.sum_mul, hws, one_mul]

/-- Independent couplings of a finite family of Monge costs all obey the
same sorted-pairing upper bound. -/
theorem sum_monge_family_couplings_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (M : κ → Matrix ι ι ℚ) (hM : ∀ k ∈ S, M k ∈ doublyStochastic ℚ ι)
    (w : κ → ℚ) (hw : ∀ k ∈ S, 0 ≤ w k)
    (H : κ → ℚ → ℚ → ℚ)
    (hH : ∀ k ∈ S, ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
      H k x₁ y₂ + H k x₂ y₁ ≤ H k x₁ y₁ + H k x₂ y₂)
    (f g : ι → ℚ) (hfg : MonovaryOn f g (Finset.univ : Finset ι)) :
    (∑ k ∈ S, w k * ∑ i, ∑ j, M k i j * H k (f i) (g j)) ≤
      ∑ k ∈ S, w k * ∑ i, H k (f i) (g i) := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (sum_monge_doublyStochastic_le (M k) (hM k hk) (H k) (hH k hk) f g hfg) (hw k hk)

/-- Padding the diagonal reduces any common subprobability marginal to the
doubly stochastic case. Thus equal weights of the individual atoms are not
required for finite Monge rearrangement. -/
theorem sum_monge_common_marginal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (r : ι → ℚ)
    (hM : ∀ i j, 0 ≤ M i j) (hr : ∀ i, r i ≤ 1)
    (hrow : ∀ i, ∑ j, M i j = r i) (hcol : ∀ j, ∑ i, M i j = r j)
    (H : ℚ → ℚ → ℚ)
    (hH : ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
      H x₁ y₂ + H x₂ y₁ ≤ H x₁ y₁ + H x₂ y₂)
    (f g : ι → ℚ) (hfg : MonovaryOn f g (Finset.univ : Finset ι)) :
    (∑ i, ∑ j, M i j * H (f i) (g j)) ≤ ∑ i, r i * H (f i) (g i) := by
  classical
  let P : Matrix ι ι ℚ := M + Matrix.diagonal (fun i => 1 - r i)
  have hP : P ∈ doublyStochastic ℚ ι := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      dsimp [P]
      apply add_nonneg (hM i j)
      simp only [Matrix.diagonal_apply]
      split_ifs
      · exact sub_nonneg.mpr (hr i)
      · exact le_rfl
    · intro i
      simp [P, Finset.sum_add_distrib, Matrix.diagonal_apply, hrow i]
    · intro j
      simp [P, Finset.sum_add_distrib, Matrix.diagonal_apply, hcol j]
  have hh := sum_monge_doublyStochastic_le P hP H hH f g hfg
  have hid : (∑ i, ∑ j, P i j * H (f i) (g j)) =
      (∑ i, ∑ j, M i j * H (f i) (g j)) +
        (∑ i, H (f i) (g i)) - ∑ i, r i * H (f i) (g i) := by
    simp only [P, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    have he : (∑ i, ∑ j, (Matrix.diagonal (fun i => 1 - r i)) i j * H (f i) (g j)) =
        (∑ i, H (f i) (g i)) - ∑ i, r i * H (f i) (g i) := by
      simp [Matrix.diagonal_apply, ite_mul, sub_mul, Finset.sum_sub_distrib]
    rw [he]
    ring
  rw [hid] at hh
  linarith

#print axioms sum_monge_common_marginal_le

#print axioms sum_monge_doublyStochastic_le
#print axioms sum_monge_family_couplings_le
end Erdos7Monge
