import Submission.RealChain

/-! One-level convex compression for mutually exclusive groups. -/
namespace Erdos7ExclusiveGroupCompression
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The exclusive-group chord bound avoids the fictitious joint value T+S. -/
theorem exclusive_chord (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (A T S t s : ℝ) (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (htT : t ≤ T) (hsS : s ≤ S)
    (he : t*s=0) :
    φ (A+t+s) ≤ φ A+(φ (A+T)-φ A)/T*t+(φ (A+S)-φ A)/S*s := by
  rcases mul_eq_zero.mp he with ht | hs
  · subst t
    simpa only [add_zero, mul_zero, zero_add] using
      Erdos7RealChain.convex_chord_majorant φ hφ A s S hs0 hsS
  · subst s
    simpa only [add_zero, mul_zero, zero_add] using
      Erdos7RealChain.convex_chord_majorant φ hφ A t T ht0 htT

/-- The two alternative groups have a three-atom convex upper law. -/
theorem exclusive_group_compression {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hm : (∑ y, μ y)=1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (A T S qt qs : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (t s : Ω → ℝ) (ht : ∀ y, 0 ≤ t y ∧ t y ≤ T)
    (hs : ∀ y, 0 ≤ s y ∧ s y ≤ S) (he : ∀ y, t y*s y=0)
    (hmt : (∑ y, μ y*t y) ≤ qt*T)
    (hms : (∑ y, μ y*s y) ≤ qs*S) :
    (∑ y, μ y*φ (A+t y+s y)) ≤
      (1-qt-qs)*φ A+qt*φ (A+T)+qs*φ (A+S) := by
  let dt := (φ (A+T)-φ A)/T
  let ds := (φ (A+S)-φ A)/S
  have hdt : 0 ≤ dt := div_nonneg (sub_nonneg.mpr (hmφ (by linarith))) hT
  have hds : 0 ≤ ds := div_nonneg (sub_nonneg.mpr (hmφ (by linarith))) hS
  have hct : T*dt=φ (A+T)-φ A := by
    by_cases h : T=0
    · simp [dt,h]
    · dsimp [dt]; field_simp
  have hcs : S*ds=φ (A+S)-φ A := by
    by_cases h : S=0
    · simp [ds,h]
    · dsimp [ds]; field_simp
  calc
    _ ≤ ∑ y, μ y*(φ A+dt*t y+ds*s y) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (exclusive_chord φ hφ A T S (t y) (s y) (ht y).1 (hs y).1
          (ht y).2 (hs y).2 (he y)) (hμ y)
    _ = φ A+dt*(∑ y, μ y*t y)+ds*(∑ y, μ y*s y) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul,hm,one_mul]
      congr 1
      · congr 1
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _; ring
      · simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _; ring
    _ ≤ φ A+dt*(qt*T)+ds*(qs*S) := by gcongr
    _ = _ := by
      calc
        _ = φ A+qt*(T*dt)+qs*(S*ds) := by ring
        _ = _ := by rw [hct,hcs]; ring

#print axioms exclusive_chord
#print axioms exclusive_group_compression
end Erdos7ExclusiveGroupCompression
