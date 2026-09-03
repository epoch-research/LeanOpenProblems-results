import Submission.RealChain

/-! One-fiber compression with an exact retained mass. Tests may be signed;
only monotonicity of their increments is used in the marginal estimate. -/
namespace Erdos7RetainedRealCompression
open scoped BigOperators
open Erdos7RealChain
set_option maxHeartbeats 1500000

/-- An exact mass and marginal upper bounds yield a retained-chain bound.
No common maximizer or independence of the coordinate events is assumed. -/
theorem retained_group_compression {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x) (m h : ℝ)
    (hmass : (∑ x, ν x) = m*h)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (a : ℝ) (W : ℕ → ℝ) (s : ℕ → Ω → ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hW : ∀ j<R, 0 ≤ W j) (hs : ∀ j<R, ∀ x, 0 ≤ s j x)
    (hsW : ∀ j<R, ∀ x, s j x ≤ W j)
    (hmarg : ∀ j<R, (∑ x, ν x*s j x) ≤ m*q j*W j) :
    (∑ x, ν x*φ (a + prefixWeight (fun j => s j x) R)) ≤
      m*(h*φ a + ∑ j ∈ Finset.range R, q j*chainIncrement φ a W j) := by
  let d (j : ℕ) := chainIncrement φ a W j / W j
  have hinc0 (j : ℕ) (hj : j<R) : 0 ≤ chainIncrement φ a W j := by
    apply sub_nonneg.mpr
    apply hmφ
    simp only [prefixWeight, Finset.sum_range_succ]
    linarith [hW j hj]
  have hd0 (j : ℕ) (hj : j<R) : 0 ≤ d j := div_nonneg (hinc0 j hj) (hW j hj)
  have hcancel (j : ℕ) : W j*d j = chainIncrement φ a W j := by
    by_cases hz : W j = 0
    · simp [d, chainIncrement, prefixWeight, Finset.sum_range_succ, hz]
    · dsimp [d]
      field_simp
  calc
    _ ≤ ∑ x, ν x*(φ a + ∑ j ∈ Finset.range R, d j*s j x) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (bounded_chain_majorant φ hφ a W (fun j => s j x) R
          (fun j hj => hs j hj x) (fun j hj => hsW j hj x)) (hν x)
    _ = m*h*φ a + ∑ j ∈ Finset.range R, d j*(∑ x, ν x*s j x) := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ m*h*φ a + ∑ j ∈ Finset.range R, d j*(m*q j*W j) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmarg j (Finset.mem_range.mp hj))
        (hd0 j (Finset.mem_range.mp hj))
    _ = _ := by
      rw [mul_add, Finset.mul_sum, mul_assoc m h]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = m*(q j*(W j*d j)) := by ring
        _ = _ := by rw [hcancel]

/-- Summation by parts preserves the actual baseline coefficient `h-q 0`.
In applications that coefficient, and every difference of q, is nonnegative. -/
theorem retained_group_mixture {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x) (m h : ℝ)
    (hmass : (∑ x, ν x) = m*h)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (a : ℝ) (W : ℕ → ℝ) (s : ℕ → Ω → ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hW : ∀ j<R, 0 ≤ W j) (hs : ∀ j<R, ∀ x, 0 ≤ s j x)
    (hsW : ∀ j<R, ∀ x, s j x ≤ W j)
    (hmarg : ∀ j<R, (∑ x, ν x*s j x) ≤ m*q j*W j) (hqR : q R=0) :
    (∑ x, ν x*φ (a + prefixWeight (fun j => s j x) R)) ≤
      m*((h-q 0)*φ a + ∑ j ∈ Finset.range R,
        (q j-q (j+1))*φ (a+prefixWeight W (j+1))) := by
  apply (retained_group_compression ν hν m h hmass φ hφ hmφ a W s q R hW hs hsW hmarg).trans_eq
  congr 1
  have hh := chain_summation_by_parts (fun j => φ (a+prefixWeight W j)) q R
  simp only [prefixWeight, Finset.range_zero, Finset.sum_empty, add_zero, hqR, zero_mul] at hh
  dsimp only [chainIncrement]
  dsimp only [prefixWeight]
  linarith

/-- A pointwise density cap bounds every nonnegative coordinate marginal. -/
lemma capped_marginal {Ω : Type*} [Fintype Ω]
    (ν w f : Ω → ℝ) (c : ℝ) (hcap : ∀ x, ν x ≤ c*w x)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x, ν x*f x) ≤ c*(∑ x, w x*f x) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcap x) (hf x))

#print axioms retained_group_mixture
end Erdos7RetainedRealCompression
