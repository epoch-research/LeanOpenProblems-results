import FormalConjecturesUtil

/-! Mixed convolution-energy bounds on a finite abelian group. These algebraic
estimates are ingredients for same-period finite families, not an infinite
construction for Erdős 66. -/
namespace Erdos66MixedEnergy
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def conv (f g : G → ℝ) (t : G) : ℝ := ∑ x, f x * g (t - x)
noncomputable def corr (f : G → ℝ) (t : G) : ℝ := ∑ x, f x * f (x + t)
noncomputable def energy (f g : G → ℝ) : ℝ := ∑ t, conv f g t ^ 2

lemma corr_neg (f : G → ℝ) (t : G) : corr f (-t) = corr f t := by
  unfold corr
  rw [← Equiv.sum_comp (Equiv.addRight t)]
  simp only [Equiv.coe_addRight, add_neg_cancel_right]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma translated_inner (g : G → ℝ) (x y : G) :
    (∑ t, g (t - x) * g (t - y)) = corr g (x - y) := by
  rw [← Equiv.sum_comp (Equiv.addRight x)]
  unfold corr
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro t ht
  congr 2
  abel

/-- The mixed convolution energy is the inner product of the two autocorrelations. -/
lemma energy_eq_corr_inner (f g : G → ℝ) :
    energy f g = ∑ t, corr f t * corr g t := by
  have hexp (t : G) : conv f g t ^ 2 =
      ∑ x : G, ∑ y : G, f x * f y * (g (t - x) * g (t - y)) := by
    unfold conv
    rw [pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  unfold energy
  simp_rw [hexp]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : G, ∑ y : G, f x * f y * corr g (x - y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.mul_sum, translated_inner]
    _ = ∑ x : G, ∑ t : G, f x * f (x - t) * corr g t := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Equiv.sum_comp (Equiv.subLeft x)]
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
    _ = ∑ t : G, (∑ x : G, f x * f (x - t)) * corr g t := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      have hh : (∑ x : G, f x * f (x - t)) = corr f t := by
        simpa only [corr, sub_eq_add_neg] using corr_neg f t
      rw [hh]

lemma energy_nonneg (f g : G → ℝ) : 0 ≤ energy f g :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma mixed_energy_sq_le (f g : G → ℝ) :
    energy f g ^ 2 ≤ energy f f * energy g g := by
  simp only [energy_eq_corr_inner, ← pow_two]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (corr f) (corr g)

/-- An `L⁴` interpolation bound, expressed without Fourier analysis. -/
lemma mixed_energy_le {f g : G → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : energy f f ≤ 2 * a ^ 2) (hg : energy g g ≤ 2 * b ^ 2) :
    energy f g ≤ 2 * a * b := by
  have hh := mixed_energy_sq_le f g
  have hm := mul_le_mul hf hg (energy_nonneg g g) (by positivity : 0 ≤ 2 * a ^ 2)
  have he := energy_nonneg f g
  have hab : 0 ≤ 2 * a * b := by positivity
  nlinarith

end Erdos66MixedEnergy
