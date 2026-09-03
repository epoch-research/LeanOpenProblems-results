import Submission.EnvelopeMulti

/-! Exact-retention dual lifting for finite families. This connects the
ordered pointwise dual split to a finite mass inequality, without a common
extremizer assumption. Coordinate geometry is an explicit hypothesis. -/
namespace Erdos7FamilyBudgetStep
open scoped BigOperators
open Erdos7EnvelopeMulti
set_option maxHeartbeats 1500000

/-- A diagonal dual bound can be pulled back across an exact-retention step.
The old arguments of the separate future families are allowed to differ. -/
theorem exact_retention_dual_step {Ω A ι : Type*} [Fintype Ω] [Fintype A]
    (S : Finset ι) (φ : ι → ℝ → ℝ) (a : ℕ → ι → ℝ)
    (U loss : ℕ → ℝ) (V : ℝ → ℝ) (lo hi : ℝ) (hlh : lo ≤ hi)
    (hφ : ∀ i ∈ S, ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i ∈ S, Monotone (φ i))
    (ha : ∀ k i, i ∈ S → 0 ≤ a k i)
    (hma : ∀ i ∈ S, Monotone (fun k => a k i)) (n : ℕ)
    (hV : ∀ x ∈ Set.Icc lo hi, 0 ≤ V x)
    (hdual : ∀ k < n, ∀ x ∈ Set.Icc lo hi,
      loss k + (∑ i ∈ S, a k i * φ i x) ≤ U k + V x)
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ν F : Ω → A → ℝ)
    (row : Ω → ℕ) (hrow : ∀ x, row x < n)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ S, ∀ x, X i x ∈ Set.Icc lo hi)
    (hmass : ∀ x, (∑ y, ν x y) = μ x * (1-loss (row x)))
    (hfuture : (∑ x, ∑ y, ν x y) ≤ ∑ x, ∑ y, ν x y*F x y)
    (hcompression : (∑ x, ∑ y, ν x y*F x y) ≤
      ∑ x, μ x*(∑ i ∈ S, a (row x) i * φ i (X i x))) :
    ∃ (b : ℝ) (h : ι → ℝ → ℝ),
      (∀ i ∈ S, ConvexOn ℝ Set.univ (h i) ∧ Monotone (h i)) ∧
      (∀ x ∈ Set.Icc lo hi, b + (∑ i ∈ S, h i x) ≤ V x) ∧
      ((∑ x, μ x) ≤ ∑ x, μ x*(U (row x) + b + ∑ i ∈ S, h i (X i x))) := by
  obtain ⟨b, h, hh, hdiag, hmaj⟩ := ordered_convex_dual_split S φ a U loss V
    lo hi hlh hφ hmφ ha hma n hV hdual
  refine ⟨b, h, hh, hdiag, ?_⟩
  have hm := hfuture.trans hcompression
  simp_rw [hmass] at hm
  have he : (∑ x, μ x) = (∑ x, μ x*(1-loss (row x))) + ∑ x, μ x*loss (row x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    _ = _ := he
    _ ≤ (∑ x, μ x*(∑ i ∈ S, a (row x) i * φ i (X i x))) +
        ∑ x, μ x*loss (row x) := add_le_add_left hm _
    _ = ∑ x, μ x*(loss (row x) + ∑ i ∈ S, a (row x) i*φ i (X i x)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
      (hmaj (row x) (hrow x) (fun i => X i x) (fun i hi => hX i hi x)) (hμ x))

/-- A finite geometric layer sum can be padded at a fixed lower count before
Jensen is applied. The scalar test need not be nonnegative. -/
lemma padded_jensen {ι : Type*} (S : Finset ι) (w X : ι → ℝ)
    (U : ℝ → ℝ) (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U)
    (lo k : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hs : (∑ i ∈ S, w i) ≤ 1)
    (hk : k ≤ (1-∑ i ∈ S, w i)*lo + ∑ i ∈ S, w i*X i) :
    U k ≤ (1-∑ i ∈ S, w i)*U lo + ∑ i ∈ S, w i*U (X i) := by
  apply (hmU hk).trans
  simpa only [smul_eq_mul] using hU.map_add_sum_le hw
    (by ring : (1-∑ i ∈ S, w i) + ∑ i ∈ S, w i = 1)
    (fun _ _ => Set.mem_univ _) (sub_nonneg.mpr hs) (Set.mem_univ lo)

#print axioms exact_retention_dual_step
#print axioms padded_jensen
end Erdos7FamilyBudgetStep
