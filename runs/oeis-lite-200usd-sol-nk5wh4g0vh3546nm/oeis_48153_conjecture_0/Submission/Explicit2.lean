import FormalConjectures.Util.ProblemImports
open Finset
noncomputable section
def chi4C : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
private lemma cpow_half_nat_eq_sqrt (k : ℕ) :
    (k : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt k : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  change (((k : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = (Real.sqrt (k : ℝ) : ℂ)
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg k) (1 / 2 : ℝ)]
  rw [← Real.sqrt_eq_rpow]

lemma chi4C_rootNumber_one : (chi4C).rootNumber = 1 := by
  rw [DirichletCharacter.rootNumber]
  have ho : (chi4C).Odd := by
    change chi4C (-1) = -1
    norm_num [chi4C, ZMod.χ₄]
  rw [if_neg ho.not_even, pow_one]
  classical
  have hc0 : chi4C (0 : ZMod 4) = 0 := by
    have h : ZMod.χ₄ (0 : ZMod 4) = 0 := by decide
    simpa [chi4C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h
  have hc1 : chi4C (1 : ZMod 4) = 1 := by
    have h : ZMod.χ₄ (1 : ZMod 4) = 1 := by decide
    simpa [chi4C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h
  have hc2 : chi4C (2 : ZMod 4) = 0 := by
    have h : ZMod.χ₄ (2 : ZMod 4) = 0 := by decide
    simpa [chi4C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h
  have hc3 : chi4C (3 : ZMod 4) = -1 := by
    have h : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
    simpa [chi4C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h
  have hs1 : (ZMod.stdAddChar : AddChar (ZMod 4) ℂ) 1 = Complex.I := by
    rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by norm_num,
      ZMod.stdAddChar_coe]
    norm_num only [Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / (4 : ℂ)) = Complex.I
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / (4 : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hs3 : (ZMod.stdAddChar : AddChar (ZMod 4) ℂ) 3 = -Complex.I := by
    rw [show (3 : ZMod 4) = ((3 : ℤ) : ZMod 4) by norm_num,
      ZMod.stdAddChar_coe]
    norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (3 : ℂ) / (4 : ℂ)) = -Complex.I
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (3 : ℂ) / (4 : ℂ) =
      (Real.pi : ℂ) * Complex.I + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    rw [Complex.exp_mul_I]
    norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  unfold gaussSum
  have hu : (Finset.univ : Finset (ZMod 4)) = {0,1,2,3} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide : (0 : ZMod 4) ∉ {(1 : ZMod 4),(2 : ZMod 4),(3 : ZMod 4)})]
  rw [Finset.sum_insert (by decide : (1 : ZMod 4) ∉ {(2 : ZMod 4),(3 : ZMod 4)})]
  rw [Finset.sum_insert (by decide : (2 : ZMod 4) ∉ {(3 : ZMod 4)})]
  rw [Finset.sum_singleton]
  rw [hc0, hc1, hc2, hc3, hs1, hs3, cpow_half_nat_eq_sqrt]
  norm_num
  rw [show (Complex.I + Complex.I) * Complex.I = -2 by
    rw [add_mul, Complex.I_mul_I]; norm_num]
  norm_num
