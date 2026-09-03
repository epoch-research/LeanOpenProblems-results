import Submission.SignedCycleWeights

/-! A finite-dimensional convex-separation certificate for fractional combinations. -/
open scoped BigOperators Classical
namespace Erdos184.FractionalDuality
set_option maxHeartbeats 800000

lemma exists_nonnegative_combination_of_dual_bound
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : I → E) (x : E) (K : ℝ) (hK : 0 < K)
    (hd : ∀ f : E →L[ℝ] ℝ, (∀ i, f (v i) ≤ 1) → f x ≤ K) :
    ∃ t : I → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) ≤ K ∧ ∑ i, t i • v i = x := by
  let a : Option I → E := fun i => i.elim 0 v
  let y : E := K⁻¹ • x
  have hy : y ∈ convexHull ℝ (Set.range a) := by
    by_contra hn
    have hclosed := (Set.finite_range a).isCompact_convexHull.isClosed
    obtain ⟨f,r,hf,hr⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range a)) hclosed hn
    have hzero : (0 : E) ∈ convexHull ℝ (Set.range a) :=
      subset_convexHull _ _ ⟨none,rfl⟩
    have hrpos : 0 < r := by simpa using hf 0 hzero
    have hbound := hd (r⁻¹ • f) (by
      intro i
      have hh := hf (a (some i)) (subset_convexHull _ _ ⟨some i,rfl⟩)
      change r⁻¹ * f (v i) ≤ 1
      rw [← div_eq_inv_mul]
      exact (div_le_one hrpos).mpr hh.le)
    change r⁻¹ * f x ≤ K at hbound
    rw [← div_eq_inv_mul] at hbound
    have hb := (div_le_iff₀ hrpos).mp hbound
    change r < f (K⁻¹ • x) at hr
    rw [map_smul,smul_eq_mul,← div_eq_inv_mul] at hr
    have hh := (lt_div_iff₀ hK).mp hr
    nlinarith
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s,w,hw,hsum,hx⟩ := hy
  let b : Option I → ℝ := fun i => if i ∈ s then w i else 0
  have hb : ∀ i, 0 ≤ b i := by intro i; dsimp [b]; split_ifs with h; exact hw i h; exact le_rfl
  have hbsum : (∑ i, b i) = 1 := by
    rw [show (∑ i, b i) = ∑ i ∈ s, w i by
      simp only [b,← Finset.sum_filter]; simp]
    exact hsum
  have hbvec : (∑ i, b i • a i) = y := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hx
    rw [show (∑ i, b i • a i) = ∑ i ∈ s, w i • a i by
      simp only [b,ite_smul,zero_smul,← Finset.sum_filter]; simp]
    exact hx
  have hcost : (∑ i : I, b (some i)) ≤ 1 := by
    rw [Fintype.sum_option] at hbsum
    linarith [hb none]
  have hvec : (∑ i : I, b (some i) • v i) = y := by
    simpa only [Fintype.sum_option,a,Option.elim_none,Option.elim_some,smul_zero,zero_add] using hbvec
  refine ⟨fun i => K * b (some i),fun i => mul_nonneg hK.le (hb _),?_,?_⟩
  · rw [← Finset.mul_sum]
    simpa using mul_le_mul_of_nonneg_left hcost hK.le
  · simp only [mul_smul]
    rw [← Finset.smul_sum,hvec]
    simp [y,smul_smul,hK.ne']

end Erdos184.FractionalDuality
