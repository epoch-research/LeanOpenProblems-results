import Submission.RealHingeComparison

/-! Capping an integer comparison law without incorrectly rounding actual
normalized counts to integers. This is an auxiliary comparison theorem. -/
namespace Erdos7CappedHingeLaw
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {Ξ : Type*} [Fintype Ξ]

noncomputable def tailMass (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k : ℕ) : ℝ :=
  ∑ z, if k ≤ Y z then ν z else 0

noncomputable def excess (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k : ℕ) : ℝ :=
  ∑ z, ν z * max 0 ((Y z : ℝ)-k)

/-- Keep the lower atoms. Replace the upper tail by two atoms at k and k+1,
preserving the mean. Positivity is exactly the tail-excess condition. -/
noncomputable def weight (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k : ℕ) : Ξ ⊕ Bool → ℝ
  | Sum.inl z => if Y z < k then ν z else 0
  | Sum.inr false => tailMass ν Y k - excess ν Y k
  | Sum.inr true => excess ν Y k

def value (Y : Ξ → ℕ) (k : ℕ) : Ξ ⊕ Bool → ℕ
  | Sum.inl z => min (Y z) k
  | Sum.inr false => k
  | Sum.inr true => k+1

lemma value_le (Y : Ξ → ℕ) (k : ℕ) (z : Ξ ⊕ Bool) : value Y k z ≤ k+1 := by
  cases z with
  | inl z => exact (Nat.min_le_right _ _).trans (by omega)
  | inr b => cases b <;> simp [value]

lemma weight_nonneg (ν : Ξ → ℝ) (hν : ∀ z, 0 ≤ ν z) (Y : Ξ → ℕ) (k : ℕ)
    (he : excess ν Y k ≤ tailMass ν Y k) (z : Ξ ⊕ Bool) : 0 ≤ weight ν Y k z := by
  have hx : 0 ≤ excess ν Y k := Finset.sum_nonneg (fun z _ =>
    mul_nonneg (hν z) (le_max_left _ _))
  cases z with
  | inl z => simp only [weight]; split_ifs <;> first | exact hν z | exact le_rfl
  | inr b => cases b <;> simp only [weight]; exact sub_nonneg.mpr he; exact hx

/-- Expectations under the capped law are expectations of the clipped
variable, plus the linear contribution of the tail excess. -/
lemma expectation_formula (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k : ℕ) (f : ℕ → ℝ) :
    (∑ z, weight ν Y k z * f (value Y k z)) =
      (∑ z, ν z * f (min (Y z) k)) + excess ν Y k * (f (k+1)-f k) := by
  have he (z : Ξ) : ν z*f (min (Y z) k) =
      (if Y z < k then ν z*f (min (Y z) k) else 0) +
      (if k ≤ Y z then ν z else 0)*f k := by
    by_cases h : Y z < k
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h, Nat.min_eq_right (Nat.le_of_not_gt h)]
  have hh : (∑ z, ν z*f (min (Y z) k)) =
      (∑ z, if Y z < k then ν z*f (min (Y z) k) else 0) + tailMass ν Y k*f k := by
    calc
      _ = ∑ z, ((if Y z < k then ν z*f (min (Y z) k) else 0) +
          (if k ≤ Y z then ν z else 0)*f k) := Finset.sum_congr rfl (fun z _ => he z)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]; rfl
  rw [hh, Fintype.sum_sum_type]
  simp only [Fintype.sum_bool, weight, value, ite_mul, zero_mul]
  ring

lemma weight_mass (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k : ℕ) :
    (∑ z, weight ν Y k z) = ∑ z, ν z := by
  simpa using expectation_formula ν Y k (fun _ => 1)

lemma clipped_add_excess (y k : ℕ) :
    ((min y k : ℕ) : ℝ)+max 0 ((y:ℝ)-k) = y := by
  by_cases h : y ≤ k
  · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · have hk : k ≤ y := by omega
    rw [min_eq_right hk, max_eq_right (sub_nonneg.mpr (by exact_mod_cast hk))]
    ring

lemma weight_mean (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k : ℕ) :
    (∑ z, weight ν Y k z * (value Y k z : ℝ)) = ∑ z, ν z * (Y z : ℝ) := by
  rw [expectation_formula]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one, excess]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_add, clipped_add_excess]

lemma clipped_hinge_add_excess (y k t : ℕ) (ht : t ≤ k) :
    max 0 (((min y k : ℕ) : ℝ)-t)+max 0 ((y:ℝ)-k) = max 0 ((y:ℝ)-t) := by
  by_cases h : y ≤ k
  · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr
      (show (y:ℝ) ≤ k by exact_mod_cast h)), add_zero]
  · have hk : k ≤ y := by omega
    have hkt : (t:ℝ) ≤ k := by exact_mod_cast ht
    have hyk : (k:ℝ) ≤ y := by exact_mod_cast hk
    rw [min_eq_right hk, max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring

/-- Every integer hinge at or below k is preserved exactly. -/
lemma weight_hinge (ν : Ξ → ℝ) (Y : Ξ → ℕ) (k t : ℕ) (ht : t ≤ k) :
    (∑ z, weight ν Y k z * max 0 ((value Y k z : ℝ)-t)) =
      ∑ z, ν z * max 0 ((Y z : ℝ)-t) := by
  rw [expectation_formula ν Y k (fun n => max 0 ((n:ℝ)-t))]
  have hkt : (t:ℝ) ≤ k := by exact_mod_cast ht
  have hd : max 0 (((k+1:ℕ):ℝ)-t)-max 0 ((k:ℝ)-t) = 1 := by
    rw [max_eq_right (by norm_num; linarith), max_eq_right (by linarith)]
    push_cast
    ring
  rw [hd, mul_one, excess, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_add, clipped_hinge_add_excess _ _ _ ht]

/-- If real counts are capped at k+1 and satisfy the raw integer-hinge bounds,
they are dominated by the positive capped law. No integer-valuedness of X is
assumed. The unused high raw hinges are discarded, not charged. -/
theorem capped_comparison {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (X : Ω → ℝ)
    (ν : Ξ → ℝ) (hν : ∀ z, 0 ≤ ν z) (Y : Ξ → ℕ) (k : ℕ)
    (he : excess ν Y k ≤ tailMass ν Y k)
    (hX : ∀ x, X x ∈ Set.Icc (0:ℝ) ((k+1:ℕ):ℝ))
    (hmass : (∑ x, μ x) = ∑ z, ν z)
    (hmean : (∑ x, μ x * X x) ≤ ∑ z, ν z * (Y z : ℝ))
    (hhinge : ∀ t ≤ k, (∑ x, μ x * max 0 (X x-t)) ≤
      ∑ z, ν z * max 0 ((Y z : ℝ)-t))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, μ x * φ (X x)) ≤ ∑ z, weight ν Y k z * φ (value Y k z) := by
  apply Erdos7RealHingeComparison.real_integer_hinge_comparison μ (weight ν Y k) X
    (value Y k) (k+1) hμ (weight_nonneg ν hν Y k he) hX (value_le Y k)
  · rw [weight_mass]
    exact hmass
  · rw [weight_mean]
    exact hmean
  · intro t ht
    by_cases htk : t+1 ≤ k
    · have hh := hhinge (t+1) htk
      have hw := weight_hinge ν Y k (t+1) htk
      push_cast at hh hw
      rw [hw]
      exact hh
    · have htk : t=k := by omega
      subst t
      have hl (x : Ω) : max 0 (X x-((k:ℝ)+1)) = 0 :=
        max_eq_left (sub_nonpos.mpr (by simpa only [Nat.cast_add, Nat.cast_one] using (hX x).2))
      have hr (z : Ξ ⊕ Bool) : max 0 ((value Y k z : ℝ)-((k:ℝ)+1)) = 0 :=
        max_eq_left (sub_nonpos.mpr (by exact_mod_cast value_le Y k z))
      simp only [hl, hr, mul_zero, Finset.sum_const_zero, le_refl]
  · exact hφ
  · exact hmφ

#print axioms weight_nonneg
#print axioms weight_hinge
#print axioms capped_comparison
end Erdos7CappedHingeLaw
