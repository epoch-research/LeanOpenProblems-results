import Submission.SmoothDivisorTail

/-! Absolute summability of the damped least-common-multiple kernel. This
supplies cutoff-independent mean-square constants for fixed positive damping. -/
namespace Erdos972DampedDivisorKernel

open Finset Filter
open scoped Topology

noncomputable def reciprocalWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * Real.log n) / n

@[simp] lemma reciprocalWeight_zero (t : ℝ) : reciprocalWeight t 0 = 0 := by
  simp [reciprocalWeight]

lemma reciprocalWeight_nonneg (t : ℝ) (n : ℕ) : 0 ≤ reciprocalWeight t n := by
  unfold reciprocalWeight
  positivity

lemma reciprocalWeight_mul (t : ℝ) (m n : ℕ) :
    reciprocalWeight t (m*n) = reciprocalWeight t m * reciprocalWeight t n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  unfold reciprocalWeight
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn),
    mul_add, Real.exp_add, mul_div_mul_comm]

lemma reciprocalWeight_square (t : ℝ) (n : ℕ) :
    (n : ℝ) * (reciprocalWeight t n)^2 = reciprocalWeight (2*t) n := by
  by_cases hn : n = 0
  · simp [hn]
  unfold reciprocalWeight
  have hexp : Real.exp (-t * Real.log n)^2 = Real.exp (-(2*t)*Real.log n) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [div_pow, hexp]
  field_simp

lemma summable_reciprocalWeight {t : ℝ} (ht : 0 < t) :
    Summable (reciprocalWeight t) := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(1+t))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply hs.congr
  intro n
  by_cases hn : n = 0
  · subst n
    rw [Nat.cast_zero, Real.zero_rpow (show -(1+t) ≠ 0 by linarith), reciprocalWeight_zero]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [show -(1+t) = -t-1 by ring, Real.rpow_sub hn0, Real.rpow_one,
    Real.rpow_def_of_pos hn0]
  simp only [reciprocalWeight]
  congr 2
  ring

def gcdIndex (z : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (Nat.gcd z.1 z.2, z.1 / Nat.gcd z.1 z.2, z.2 / Nat.gcd z.1 z.2)

lemma gcdIndex_injective : Function.Injective gcdIndex := by
  intro x y h
  have h₁ := congrArg (fun z : ℕ × (ℕ × ℕ) => z.1*z.2.1) h
  have h₂ := congrArg (fun z : ℕ × (ℕ × ℕ) => z.1*z.2.2) h
  simp only [gcdIndex, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] at h₁
  simp only [gcdIndex, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)] at h₂
  exact Prod.ext h₁ h₂

noncomputable def kernel (t : ℝ) (z : ℕ × ℕ) : ℝ :=
  (Nat.gcd z.1 z.2 : ℝ) * reciprocalWeight t z.1 * reciprocalWeight t z.2

lemma kernel_nonneg (t : ℝ) (z : ℕ × ℕ) : 0 ≤ kernel t z := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (reciprocalWeight_nonneg _ _))
    (reciprocalWeight_nonneg _ _)

lemma kernel_gcdIndex (t : ℝ) (z : ℕ × ℕ) :
    kernel t z = reciprocalWeight (2*t) (gcdIndex z).1 *
      (reciprocalWeight t (gcdIndex z).2.1 * reciprocalWeight t (gcdIndex z).2.2) := by
  have h₁ : reciprocalWeight t z.1 = reciprocalWeight t (Nat.gcd z.1 z.2) *
      reciprocalWeight t (z.1 / Nat.gcd z.1 z.2) := by
    rw [← reciprocalWeight_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  have h₂ : reciprocalWeight t z.2 = reciprocalWeight t (Nat.gcd z.1 z.2) *
      reciprocalWeight t (z.2 / Nat.gcd z.1 z.2) := by
    rw [← reciprocalWeight_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
  unfold kernel gcdIndex
  rw [h₁, h₂, ← reciprocalWeight_square]
  ring

/-- The pair series converges for every positive t, not just t>1/2. -/
theorem summable_kernel {t : ℝ} (ht : 0 < t) : Summable (kernel t) := by
  have hs := summable_reciprocalWeight ht
  have hss := hs.mul_of_nonneg hs (reciprocalWeight_nonneg t) (reciprocalWeight_nonneg t)
  have htriple := (summable_reciprocalWeight (show 0 < 2*t by positivity)).mul_of_nonneg hss
    (reciprocalWeight_nonneg (2*t))
    (fun z : ℕ × ℕ => mul_nonneg (reciprocalWeight_nonneg t z.1) (reciprocalWeight_nonneg t z.2))
  apply (htriple.comp_injective gcdIndex_injective).congr
  intro z
  exact (kernel_gcdIndex t z).symm

lemma kernel_lcm {t : ℝ} {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    kernel t (d,e) =
      Real.exp (-t*Real.log d) * Real.exp (-t*Real.log e) / (Nat.lcm d e : ℝ) := by
  have hl : (Nat.lcm d e : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero hd.ne' he.ne')
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hge : (Nat.gcd d e : ℝ)*(Nat.lcm d e : ℝ) = (d : ℝ)*e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  unfold kernel reciprocalWeight
  dsimp only
  field_simp
  nlinarith only [hge]

noncomputable def kernelMass (t : ℝ) : ℝ := ∑' z : ℕ × ℕ, kernel t z

lemma kernelMass_nonneg (t : ℝ) : 0 ≤ kernelMass t :=
  tsum_nonneg (kernel_nonneg t)

#print axioms summable_kernel
#print axioms kernel_lcm

end Erdos972DampedDivisorKernel
