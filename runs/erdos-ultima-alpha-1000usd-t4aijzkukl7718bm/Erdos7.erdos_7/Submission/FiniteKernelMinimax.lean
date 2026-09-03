import FormalConjecturesUtil

/-! A finite-dimensional minimax criterion for one simultaneous kernel.
A separate kernel for each test is insufficient. One must be able to respond
to every probability-weighted combination of the tests. The compact convex
criterion below states that quantifier exchange precisely. It does not supply
the quantitative covering-system estimates required to apply it. -/
namespace Erdos7FiniteKernelMinimax
open scoped BigOperators
open Set
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma functional_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℝ) →L[ℝ] ℝ) (z : I → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  have hz : z = ∑ i, z i • (Pi.single i (1 : ℝ) : I → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

/-- A nonempty compact convex set in a finite real coordinate space meets
its nonnegative orthant iff it defeats every probability-weighted linear test.
This is a finite-dimensional minimax/Farkas criterion, not a covering result. -/
theorem exists_nonnegative_iff {I : Type*} [Fintype I]
    (S : Set (I → ℝ)) (hne : S.Nonempty) (hc : Convex ℝ S) (hk : IsCompact S) :
    (∃ z ∈ S, ∀ i, 0 ≤ z i) ↔
      ∀ w : I → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
        ∃ z ∈ S, 0 ≤ ∑ i, w i * z i := by
  classical
  constructor
  · rintro ⟨z, hz, hpos⟩ w hw _
    exact ⟨z, hz, Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hpos i))⟩
  · intro hall
    by_contra hnone
    have hdis : Disjoint S (ProperCone.positive ℝ (I → ℝ) : Set (I → ℝ)) := by
      apply Set.disjoint_left.mpr
      intro z hz hpos
      exact hnone ⟨z, hz, hpos⟩
    obtain ⟨f, hfpos, hfneg⟩ := (ProperCone.positive ℝ (I → ℝ)).hyperplane_separation hc hk hdis
    let w : I → ℝ := fun i => f (Pi.single i 1)
    have hw : ∀ i, 0 ≤ w i := by
      intro i
      apply hfpos
      change 0 ≤ (Pi.single i (1 : ℝ) : I → ℝ)
      intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have hws : 0 < ∑ i, w i := by
      have hn : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
      by_contra h
      have hz : (∑ i, w i) = 0 := by linarith
      have hwz : ∀ i, w i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp hz i (Finset.mem_univ i)
      obtain ⟨z, hzS⟩ := hne
      have hfn := hfneg z hzS
      rw [functional_coordinates] at hfn
      change (∑ i, w i * z i) < 0 at hfn
      simp [hwz] at hfn
    obtain ⟨z, hz, hwz⟩ := hall (fun i => w i / ∑ j, w j)
      (fun i => div_nonneg (hw i) hws.le) (by rw [← Finset.sum_div]; exact div_self hws.ne')
    have hfn := hfneg z hz
    rw [functional_coordinates] at hfn
    change (∑ i, w i * z i) < 0 at hfn
    have he : (∑ i, (w i / ∑ j, w j) * z i) =
        (∑ i, w i * z i) / ∑ j, w j := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hwz
    exact (not_lt_of_ge hwz) (div_neg_of_neg_of_pos hfn hws)

/-- Simultaneous bounds on finitely many affine costs over a compact convex
feasible set. Responding to every mixture is equivalent to a single feasible
choice satisfying every bound. For kernel applications, the coordinates of
`x` are the kernel entries and the affine costs are weighted test integrals. -/
theorem exists_common_choice_iff {I J : Type*} [Fintype I] [Fintype J]
    (K : Set (J → ℝ)) (hne : K.Nonempty) (hc : Convex ℝ K) (hk : IsCompact K)
    (f : (J → ℝ) →ᵃ[ℝ] (I → ℝ)) (hf : Continuous f) (b : I → ℝ) :
    (∃ x ∈ K, ∀ i, f x i ≤ b i) ↔
      ∀ w : I → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
        ∃ x ∈ K, (∑ i, w i * f x i) ≤ ∑ i, w i * b i := by
  classical
  constructor
  · rintro ⟨x, hx, hb⟩ w hw _
    exact ⟨x, hx, Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))⟩
  · intro hall
    let g : (J → ℝ) →ᵃ[ℝ] (I → ℝ) := AffineMap.const ℝ (J → ℝ) b - f
    have hg : Continuous g := by
      change Continuous (fun x => b - f x)
      exact continuous_const.sub hf
    have himage : ∃ z ∈ g '' K, ∀ i, 0 ≤ z i := by
      apply (exists_nonnegative_iff (g '' K) (hne.image g) (hc.affine_image g) (hk.image hg)).mpr
      intro w hw hsum
      obtain ⟨x, hx, hcost⟩ := hall w hw hsum
      refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
      change 0 ≤ ∑ i, w i * (b i - f x i)
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      exact sub_nonneg.mpr hcost
    obtain ⟨z, ⟨x, hx, rfl⟩, hpos⟩ := himage
    refine ⟨x, hx, fun i => ?_⟩
    exact sub_nonneg.mp (hpos i)

#print axioms exists_nonnegative_iff
#print axioms exists_common_choice_iff
end Erdos7FiniteKernelMinimax
