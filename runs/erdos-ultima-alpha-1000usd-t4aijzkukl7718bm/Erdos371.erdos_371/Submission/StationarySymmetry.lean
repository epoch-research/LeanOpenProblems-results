import FormalConjecturesUtil

/-!
A sufficient symmetry principle for a possible ergodic approach.
No claim is made here that the prime-factor process satisfies its hypotheses.
-/

namespace Erdos371

open Filter
open scoped Topology

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If a correlation of a contraction is constant at every positive gap, its
value is the correlation with the orthogonal projection to the fixed space. -/
lemma gap_invariant_inner_eq_projection (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1) (v w : E)
    (hgap : ∀ k : ℕ, 0 < k → inner ℝ v ((T : E → E)^[k] w) = inner ℝ v (T w)) :
    inner ℝ v (T w) = inner ℝ v ((LinearMap.eqLocus T 1).starProjection w) := by
  have hc : Tendsto (fun k : ℕ => inner ℝ v ((T : E → E)^[k] w)) atTop
      (nhds (inner ℝ v (T w))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (hgap k hk).symm
  have hav := hc.cesaro
  have hp := tendsto_const_nhds.inner (T.tendsto_birkhoffAverage_orthogonalProjection hT w)
    (𝕜 := ℝ) (x := v)
  have he (N : ℕ) :
      (N : ℝ)⁻¹ * (∑ k ∈ Finset.range N, inner ℝ v ((T : E → E)^[k] w)) =
      inner ℝ v (birkhoffAverage ℝ T id N w) := by
    simp [birkhoffAverage, birkhoffSum, inner_smul_right, inner_sum]
  simp_rw [he] at hav
  exact tendsto_nhds_unique hav hp

/-- Gap invariance in both orientations forces their equality. The missing
arithmetic issue is establishing this invariance, not the Hilbert-space step. -/
theorem gap_invariant_inner_symmetric (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1) (v w : E)
    (hvw : ∀ k : ℕ, 0 < k → inner ℝ v ((T : E → E)^[k] w) = inner ℝ v (T w))
    (hwv : ∀ k : ℕ, 0 < k → inner ℝ w ((T : E → E)^[k] v) = inner ℝ w (T v)) :
    inner ℝ v (T w) = inner ℝ w (T v) := by
  rw [gap_invariant_inner_eq_projection T hT v w hvw,
    gap_invariant_inner_eq_projection T hT w v hwv,
    ← Submodule.inner_starProjection_left_eq_right]
  exact real_inner_comm _ _

end Hilbert

/-- For a symmetric finite joint distribution, the mass above the diagonal is
half the mass off the diagonal. The positivity assumptions are not needed for
this algebraic identity. -/
lemma symmetric_matrix_above_diagonal {ι : Type*} [Fintype ι] [LinearOrder ι]
    (C : ι → ι → ℝ) (hsym : ∀ i j, C i j = C j i) (htotal : ∑ i, ∑ j, C i j = 1) :
    (∑ i, ∑ j, if i < j then C i j else 0) = (1 - ∑ i, C i i) / 2 := by
  classical
  have he : (∑ i, ∑ j, if j < i then C i j else 0) =
      ∑ i, ∑ j, if i < j then C i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  have hterm (i j : ι) :
      (if i < j then C i j else 0) + (if j < i then C i j else 0) +
        (if j = i then C i i else 0) = C i j := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt, h.ne']
    · simp [h]
    · simp [h, h.not_gt, h.ne]
  have hsum : (∑ i, ∑ j, if i < j then C i j else 0) +
      (∑ i, ∑ j, if j < i then C i j else 0) + (∑ i, C i i) = 1 := by
    have hd : (∑ i, ∑ j, if j = i then C i i else 0) = ∑ i, C i i := by simp
    rw [← hd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, hterm]
    exact htotal
  rw [he] at hsum
  linarith

/-- A finite-label consequence of gap-invariant correlations. It does not
supply gap invariance for the largest-prime-factor process. -/
theorem gap_invariant_transition_balance {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Fintype ι] [LinearOrder ι]
    (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1) (v : ι → E)
    (hgap : ∀ i j (k : ℕ), 0 < k →
      inner ℝ (v i) ((T : E → E)^[k] (v j)) = inner ℝ (v i) (T (v j)))
    (htotal : ∑ i, ∑ j, inner ℝ (v i) (T (v j)) = 1) :
    (∑ i, ∑ j, if i < j then inner ℝ (v i) (T (v j)) else 0) =
      (1 - ∑ i, inner ℝ (v i) (T (v i))) / 2 := by
  exact symmetric_matrix_above_diagonal _
    (fun i j => gap_invariant_inner_symmetric T hT (v i) (v j) (hgap i j) (hgap j i)) htotal

#print axioms gap_invariant_inner_symmetric
#print axioms gap_invariant_transition_balance
end Erdos371
