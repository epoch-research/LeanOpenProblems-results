import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# An auxiliary quartic obstruction over the Gaussian integers

A sum of four fourth powers in `GaussianInt` can vanish only when every
summand is zero.  The proof uses the real parts modulo eight to show that
`1 + i` divides every coordinate, followed by descent on the sum of norms.

This is only the four-term quartic obstruction, not a global representation
bound or a resolution of a conjecture about such bounds.
-/

namespace QuarticObstruction

open scoped BigOperators

/-- The real part of a Gaussian fourth power. -/
theorem re_pow_four (z : GaussianInt) :
    (z ^ 4).re = z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4 := by
  simp only [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two,
    Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

/-- Modulo eight, a fourth power has real part `0`, `4`, or `1`.
The first two cases have equal coordinate parities, and the last does not. -/
theorem quartic_residue_mod_eight (z : GaussianInt) :
    ((z ^ 4).re % 8 = 0 ∧ z.re % 2 = z.im % 2) ∨
    ((z ^ 4).re % 8 = 4 ∧ z.re % 2 = z.im % 2) ∨
    ((z ^ 4).re % 8 = 1 ∧ z.re % 2 ≠ z.im % 2) := by
  have hmod : (z ^ 4).re % 8 =
      ((z.re % 8) ^ 4 - 6 * (z.re % 8) ^ 2 * (z.im % 8) ^ 2 +
        (z.im % 8) ^ 4) % 8 := by
    rw [re_pow_four]
    have ha := (Int.mod_modEq z.re 8).symm
    have hb := (Int.mod_modEq z.im 8).symm
    exact ((ha.pow 4).sub (((ha.pow 2).mul_left 6).mul (hb.pow 2))).add (hb.pow 4)
  have hre : z.re % 2 = (z.re % 8) % 2 := by omega
  have him : z.im % 2 = (z.im % 8) % 2 := by omega
  rw [hmod, hre, him]
  have ha0 := Int.emod_nonneg z.re (by norm_num : (8 : ℤ) ≠ 0)
  have ha8 := Int.emod_lt_of_pos z.re (by norm_num : (0 : ℤ) < 8)
  have hb0 := Int.emod_nonneg z.im (by norm_num : (8 : ℤ) ≠ 0)
  have hb8 := Int.emod_lt_of_pos z.im (by norm_num : (0 : ℤ) < 8)
  interval_cases z.re % 8 <;> interval_cases z.im % 8 <;> norm_num

/-- The four-term mod-eight obstruction: every coordinate is divisible by `1 + i`. -/
theorem same_parity_of_sum_fourth_powers_eq_zero (z : Fin 4 → GaussianInt)
    (h : ∑ i, z i ^ 4 = 0) : ∀ i, (z i).re % 2 = (z i).im % 2 := by
  have hr := congrArg Zsqrtd.re h
  simp [Fin.sum_univ_succ] at hr
  have h0 := quartic_residue_mod_eight (z 0)
  have h1 := quartic_residue_mod_eight (z 1)
  have h2 := quartic_residue_mod_eight (z 2)
  have h3 := quartic_residue_mod_eight (z 3)
  have hp :
      (z 0).re % 2 = (z 0).im % 2 ∧
      (z 1).re % 2 = (z 1).im % 2 ∧
      (z 2).re % 2 = (z 2).im % 2 ∧
      (z 3).re % 2 = (z 3).im % 2 := by omega
  intro i
  fin_cases i
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2

/-- The Gaussian prime `1 + i`. -/
def oneAddI : GaussianInt := ⟨1, 1⟩

/-- Explicit division by `1 + i`, exact when the two coordinates have the same parity. -/
def divOneAddI (z : GaussianInt) : GaussianInt :=
  ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩

theorem oneAddI_ne_zero : oneAddI ≠ 0 := by
  decide

theorem norm_oneAddI : Zsqrtd.norm oneAddI = 2 := by
  norm_num [oneAddI, Zsqrtd.norm]

/-- Equal coordinate parities make the explicit division exact. -/
theorem oneAddI_mul_divOneAddI (z : GaussianInt)
    (h : z.re % 2 = z.im % 2) : oneAddI * divOneAddI z = z := by
  ext <;> simp [oneAddI, divOneAddI, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> omega

/-- A natural-number descent measure: the sum of the four squared absolute values. -/
def totalNorm (z : Fin 4 → GaussianInt) : ℕ :=
  ∑ i, (Zsqrtd.norm (z i)).natAbs

theorem totalNorm_eq_zero_iff (z : Fin 4 → GaussianInt) :
    totalNorm z = 0 ↔ ∀ i, z i = 0 := by
  simp [totalNorm, GaussianInt.norm_eq_zero]

/-- Dividing all four coordinates by `1 + i` preserves the equation and halves
its total norm. -/
theorem descent (z : Fin 4 → GaussianInt) (h : ∑ i, z i ^ 4 = 0) :
    ∃ w : Fin 4 → GaussianInt,
      (∀ i, oneAddI * w i = z i) ∧
      (∑ i, w i ^ 4 = 0) ∧ totalNorm z = 2 * totalNorm w := by
  let w : Fin 4 → GaussianInt := fun i => divOneAddI (z i)
  have hf (i : Fin 4) : oneAddI * w i = z i :=
    oneAddI_mul_divOneAddI (z i) (same_parity_of_sum_fourth_powers_eq_zero z h i)
  refine ⟨w, hf, ?_, ?_⟩
  · have hm : oneAddI ^ 4 * (∑ i, w i ^ 4) = 0 := by
      calc
        oneAddI ^ 4 * (∑ i, w i ^ 4) = ∑ i, (oneAddI * w i) ^ 4 := by
          simp [Finset.mul_sum, mul_pow]
        _ = ∑ i, z i ^ 4 := by simp_rw [hf]
        _ = 0 := h
    exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ oneAddI_ne_zero)
  · unfold totalNorm
    calc
      (∑ i, (Zsqrtd.norm (z i)).natAbs) = ∑ i, 2 * (Zsqrtd.norm (w i)).natAbs := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hf i, Zsqrtd.norm_mul, Int.natAbs_mul, norm_oneAddI]
        norm_num
      _ = 2 * ∑ i, (Zsqrtd.norm (w i)).natAbs := (Finset.mul_sum _ _ _).symm

/-- Four Gaussian-integer fourth powers sum to zero only for the zero tuple. -/
theorem sum_fourth_powers_eq_zero (z : Fin 4 → GaussianInt)
    (h : ∑ i, z i ^ 4 = 0) : ∀ i, z i = 0 := by
  suffices ∀ n : ℕ, ∀ z : Fin 4 → GaussianInt,
      totalNorm z = n → (∑ i, z i ^ 4 = 0) → ∀ i, z i = 0 from
    this (totalNorm z) z rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro z hn hz
      by_cases hn0 : n = 0
      · exact (totalNorm_eq_zero_iff z).mp (hn.trans hn0)
      · obtain ⟨w, hf, hw, hnorm⟩ := descent z hz
        have hlt : totalNorm w < n := by omega
        have hw0 := ih (totalNorm w) hlt w rfl hw
        intro i
        rw [← hf i, hw0 i, mul_zero]

/-- The exact `Fin 4` obstruction, as an equivalence. -/
theorem sum_fourth_powers_eq_zero_iff (z : Fin 4 → GaussianInt) :
    (∑ i, z i ^ 4 = 0) ↔ ∀ i, z i = 0 := by
  constructor
  · exact sum_fourth_powers_eq_zero z
  · intro h
    simp [h]

end QuarticObstruction

#print axioms QuarticObstruction.quartic_residue_mod_eight
#print axioms QuarticObstruction.same_parity_of_sum_fourth_powers_eq_zero
#print axioms QuarticObstruction.descent
#print axioms QuarticObstruction.sum_fourth_powers_eq_zero
#print axioms QuarticObstruction.sum_fourth_powers_eq_zero_iff
