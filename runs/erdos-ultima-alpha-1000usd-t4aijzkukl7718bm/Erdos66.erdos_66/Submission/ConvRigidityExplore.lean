import Submission.MixedEnergyExplore

/-! Quantitative rigidity of a self-convolution near uniform measure on a
finite abelian group. This is a necessary-condition tool, not a settlement. -/
namespace Erdos66ConvRigidity
open Erdos66MixedEnergy
open Filter
open scoped Topology
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma point_fourth_le_energy (f : G → ℝ) (x : G) : f x ^ 4 ≤ energy f f := by
  classical
  have h₁ : f x ^ 2 ≤ ∑ y : G, f y ^ 2 :=
    Finset.single_le_sum (fun y _ ↦ sq_nonneg (f y)) (Finset.mem_univ x)
  have h₂ : (∑ y : G, f y ^ 2) ^ 2 ≤ energy f f := by
    rw [energy_eq_corr_inner]
    have hh := Finset.single_le_sum (f := fun t ↦ corr f t * corr f t)
      (fun t _ ↦ mul_self_nonneg _) (Finset.mem_univ (0 : G))
    simpa only [corr, add_zero, ← pow_two] using hh
  have h₀ : 0 ≤ ∑ y : G, f y ^ 2 := Finset.sum_nonneg (fun y _ ↦ sq_nonneg _)
  nlinarith [sq_nonneg (f x ^ 2 - ∑ y : G, f y ^ 2)]

lemma sum_sub_perm (f : G → ℝ) (t : G) : (∑ x : G, f (t - x)) = ∑ x : G, f x :=
  Equiv.sum_comp (Equiv.subLeft t) f

lemma conv_centered (f : G → ℝ) (a : ℝ) (t : G) :
    conv (fun x ↦ f x - a) (fun x ↦ f x - a) t =
      conv f f t - 2 * a * (∑ x, f x) + Fintype.card G * a ^ 2 := by
  unfold conv
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, sum_sub_perm]
  ring

lemma conv_centered_probability (f : G → ℝ) (hf : ∑ x, f x = 1) (t : G) :
    conv (fun x ↦ f x - 1 / Fintype.card G) (fun x ↦ f x - 1 / Fintype.card G) t =
      conv f f t - 1 / Fintype.card G := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [conv_centered, hf]
  field_simp
  ring

/-- Fourth-power control avoids choosing Fourier characters. -/
theorem probability_stability (f : G → ℝ) (hf : ∑ x, f x = 1) (x : G) :
    (f x - 1 / Fintype.card G) ^ 4 ≤
      ∑ t : G, (conv f f t - 1 / Fintype.card G) ^ 2 := by
  have hh := point_fourth_le_energy (fun x ↦ f x - 1 / Fintype.card G) x
  simpa only [energy, conv_centered_probability f hf] using hh

theorem probability_rigidity (f : G → ℝ) (hf : ∑ x, f x = 1)
    (hc : ∀ t, conv f f t = 1 / Fintype.card G) :
    ∀ x, f x = 1 / Fintype.card G := by
  intro x
  have hh := probability_stability f hf x
  simp only [hc, sub_self, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero] at hh
  have hz : (f x - 1 / Fintype.card G) ^ 4 = 0 := le_antisymm hh (by positivity)
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

/-- Uniform convolution in the limit forces uniform mass in the limit. The
vectors themselves need not have nonnegative coordinates. -/
theorem tendsto_probability_of_convolution {ι : Type*} {L : Filter ι}
    (f : ι → G → ℝ) (hf : ∀ᶠ i in L, ∑ x, f i x = 1)
    (hc : ∀ t, Tendsto (fun i ↦ conv (f i) (f i) t) L (𝓝 (1 / Fintype.card G)))
    (x : G) : Tendsto (fun i ↦ f i x) L (𝓝 (1 / Fintype.card G)) := by
  classical
  have hlim : Tendsto (fun i ↦ ∑ t : G, (conv (f i) (f i) t - 1 / Fintype.card G) ^ 2)
      L (𝓝 0) := by
    simpa only [sub_self, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun t _ ↦ ((hc t).sub_const (1 / Fintype.card G)).pow 2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hf, hlim.eventually_lt_const (pow_pos hε 4)] with i hi hE
  have hb := (probability_stability (f i) hi x).trans_lt hE
  rw [Real.dist_eq]
  apply (pow_lt_pow_iff_left₀ (abs_nonneg _) hε.le (by omega : 4 ≠ 0)).mp
  simpa only [show (4 : ℕ) = 2 * 2 by omega, pow_mul, sq_abs] using hb


end Erdos66ConvRigidity
