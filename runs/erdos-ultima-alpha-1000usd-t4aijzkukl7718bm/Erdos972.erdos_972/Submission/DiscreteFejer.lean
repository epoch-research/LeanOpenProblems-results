import Submission.PrimeFejer

/-! A discrete Fejér partition of unity and weighted Fourier quadrature.
All results apply to an arbitrary finite weighted collection of points. -/
namespace Erdos972DiscreteFejer

open Finset Complex
open scoped ComplexConjugate
open Erdos972ExponentialSum Erdos972PrimeFejer

lemma sum_zmod_val {H : ℕ} [NeZero H] {E : Type*} [AddCommMonoid E] (f : ℕ → E) :
    (∑ k : ZMod H, f k.val) = ∑ j ∈ range H, f j := by
  classical
  apply sum_bij (fun k _ => k.val)
  · intro k _
    exact mem_range.mpr k.val_lt
  · intro k _ l _ he
    exact ZMod.val_injective H he
  · intro j hj
    refine ⟨(j : ZMod H), mem_univ _, ?_⟩
    exact (ZMod.val_natCast H j).trans (Nat.mod_eq_of_lt (mem_range.mp hj))
  · intro k _
    rfl

lemma kernel_eq_finiteFourier {H : ℕ} [NeZero H] (x : ℝ) (k : ZMod H) :
    dirichletKernel H (x - (k.val : ℝ) / H) =
      finiteFourier (fun m : ZMod H => phase (x * m.val)) (-k) := by
  unfold finiteFourier dirichletKernel
  rw [← sum_zmod_val]
  apply sum_congr rfl
  intro m _
  have hc : ZMod.stdAddChar (k * m) = phase ((k.val : ℝ) / H * m.val) := by
    have hh := rational_phase_nat (q := H) 1 (Nat.coprime_one_left H) k.val m.val
    simpa only [ZMod.coe_unitOfCoprime, Nat.cast_one, one_mul, ZMod.natCast_zmod_val,
      one_div_mul_eq_div] using hh
  rw [neg_mul, ← conjugate_character, hc, conjugate_phase, ← phase_add]
  congr 1
  ring

/-- The shifted Dirichlet-kernel energies form an exact finite partition. -/
lemma kernel_grid_sum {H : ℕ} [NeZero H] (x : ℝ) :
    (∑ k : ZMod H, ‖dirichletKernel H (x - (k.val : ℝ) / H)‖ ^ 2) = (H : ℝ) ^ 2 := by
  simp_rw [kernel_eq_finiteFourier]
  have he := Equiv.sum_comp (Equiv.neg (ZMod H))
    (fun k => ‖finiteFourier (fun m : ZMod H => phase (x * m.val)) k‖ ^ 2)
  change (∑ k : ZMod H, ‖finiteFourier (fun m : ZMod H => phase (x * m.val)) (-k)‖ ^ 2) = _ at he
  rw [he]
  rw [finiteFourier_energy]
  simp only [norm_phase, one_pow, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  ring

noncomputable def kernelWeight (H : ℕ) (x t : ℝ) : ℝ :=
  ‖dirichletKernel H (x - t)‖ ^ 2 / (H : ℝ) ^ 2

lemma kernelWeight_nonneg (H : ℕ) (x t : ℝ) : 0 ≤ kernelWeight H x t := by
  unfold kernelWeight
  positivity

lemma kernelWeight_grid_sum {H : ℕ} [NeZero H] (x : ℝ) :
    (∑ k : ZMod H, kernelWeight H x ((k.val : ℝ) / H)) = 1 := by
  simp only [kernelWeight, ← sum_div, kernel_grid_sum]
  exact div_self (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne H)))

lemma kernelWeight_le_of_far {H : ℕ} [NeZero H] {x t δ : ℝ} (hδ : 0 < δ)
    (hfar : δ ≤ ‖phase (x - t) - 1‖) :
    kernelWeight H x t ≤ 4 / (δ ^ 2 * (H : ℝ) ^ 2) := by
  unfold kernelWeight
  rw [← div_div]
  exact div_le_div_of_nonneg_right (dirichletKernel_sq_le_of_avoids H (x-t) δ hδ hfar)
    (sq_nonneg _)

noncomputable def weightedFourier {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (h : ℝ) : ℂ :=
  ∑ n ∈ s, (w n : ℂ) * phase (h * x n)

lemma weightedFourier_zero {ι : Type*} (s : Finset ι) (w x : ι → ℝ) :
    weightedFourier s w x 0 = (∑ n ∈ s, w n : ℝ) := by
  simp only [weightedFourier, zero_mul, phase, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, Complex.ofReal_sum]

lemma kernel_energy_fourier {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (H : ℕ) (t : ℝ) :
    ((∑ n ∈ s, w n * ‖dirichletKernel H (x n - t)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ range H, ∑ j ∈ range H,
        phase (-((i : ℝ) - j) * t) * weightedFourier s w x ((i : ℝ) - j) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, dirichletKernel_energy, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  unfold weightedFourier
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [show ((i : ℝ) - j) * (x n - t) = -((i : ℝ) - j) * t + ((i : ℝ) - j) * x n by ring,
    phase_add]
  ring

/-- Fourier cancellation controls each kernel average with an explicit error. -/
lemma weighted_kernel_discrepancy {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    {H : ℕ} [NeZero H] (t E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ i j : ℕ, i < H → j < H → i ≠ j →
      ‖weightedFourier s w x ((i : ℝ) - j)‖ ≤ E) :
    |(∑ n ∈ s, w n * kernelWeight H (x n) t) - (∑ n ∈ s, w n) / H| ≤ E := by
  let W := ∑ n ∈ s, w n
  let A : ℕ → ℕ → ℂ := fun i j =>
    phase (-((i : ℝ) - j) * t) * weightedFourier s w x ((i : ℝ) - j)
  have hdiag (i : ℕ) : A i i = (W : ℂ) := by
    simp only [A, sub_self, neg_zero, zero_mul, weightedFourier_zero, phase,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, W]
  have hpoint (i j : ℕ) (hi : i ∈ range H) (hj : j ∈ range H) :
      ‖A i j - (if i = j then (W : ℂ) else 0)‖ ≤ E := by
    by_cases hij : i = j
    · subst j
      simpa only [if_true, hdiag, sub_self, norm_zero] using hE0
    · rw [if_neg hij, sub_zero]
      dsimp [A]
      rw [norm_mul, norm_phase, one_mul]
      exact hE i j (mem_range.mp hi) (mem_range.mp hj) hij
  have he : (((∑ n ∈ s, w n * ‖dirichletKernel H (x n - t)‖ ^ 2) - H * W : ℝ) : ℂ) =
      ∑ i ∈ range H, ∑ j ∈ range H, (A i j - if i = j then (W : ℂ) else 0) := by
    simp only [sum_sub_distrib, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast]
    rw [kernel_energy_fourier]
    congr 1
    simp only [sum_ite_eq, mem_range]
    simp only [sum_congr rfl (fun i hi => if_pos (mem_range.mp hi)), sum_const, card_range,
      nsmul_eq_mul]
  have hb : |(∑ n ∈ s, w n * ‖dirichletKernel H (x n - t)‖ ^ 2) - H * W| ≤ (H : ℝ) ^ 2 * E := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, he]
    calc
      _ ≤ ∑ i ∈ range H, ‖∑ j ∈ range H, (A i j - if i = j then (W : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range H, ∑ j ∈ range H, E := by
        exact sum_le_sum (fun i hi => (norm_sum_le _ _).trans (sum_le_sum (fun j hj => hpoint i j hi hj)))
      _ = _ := by simp; ring
  have hH0 : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne H)
  have he' : (∑ n ∈ s, w n * kernelWeight H (x n) t) - W / H =
      ((∑ n ∈ s, w n * ‖dirichletKernel H (x n - t)‖ ^ 2) - H * W) / (H : ℝ) ^ 2 := by
    simp only [kernelWeight, ← mul_div_assoc, ← sum_div]
    field_simp
  rw [he', abs_div, abs_of_nonneg (sq_nonneg (H : ℝ))]
  exact (div_le_iff₀ (sq_pos_of_ne_zero hH0)).mpr (by simpa only [mul_comm E] using hb)

/-- Summing selected grid nodes approximates their uniform grid mass. -/
lemma weighted_grid_discrepancy {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    {H : ℕ} [NeZero H] (J : Finset (ZMod H)) (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ i j : ℕ, i < H → j < H → i ≠ j →
      ‖weightedFourier s w x ((i : ℝ) - j)‖ ≤ E) :
    |(∑ n ∈ s, w n * ∑ k ∈ J, kernelWeight H (x n) ((k.val : ℝ) / H)) -
      (J.card : ℝ) / H * (∑ n ∈ s, w n)| ≤ (J.card : ℝ) * E := by
  have he : (∑ n ∈ s, w n * ∑ k ∈ J, kernelWeight H (x n) ((k.val : ℝ) / H)) -
      (J.card : ℝ) / H * (∑ n ∈ s, w n) =
      ∑ k ∈ J, ((∑ n ∈ s, w n * kernelWeight H (x n) ((k.val : ℝ) / H)) - (∑ n ∈ s, w n) / H) := by
    calc
      _ = (∑ k ∈ J, ∑ n ∈ s, w n * kernelWeight H (x n) ((k.val : ℝ) / H)) -
          (J.card : ℝ) / H * (∑ n ∈ s, w n) := by
        congr 1
        simp only [mul_sum]
        exact sum_comm
      _ = _ := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
        ring
  rw [he]
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun k hk =>
    weighted_kernel_discrepancy s w x ((k.val : ℝ) / H) E hE0 hE)).trans_eq (by simp))

#print axioms kernelWeight_grid_sum
#print axioms weighted_grid_discrepancy

end Erdos972DiscreteFejer
