import FormalConjectures.Util.ProblemImports
open Finset
noncomputable section

def chi8C : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
def chi8'C : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)
private lemma cpow_half_nat_eq_sqrt (k : ℕ) :
    (k : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt k : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  change (((k : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) = (Real.sqrt (k : ℝ) : ℂ)
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg k) (1 / 2 : ℝ)]
  rw [← Real.sqrt_eq_rpow]

private lemma sqrt8_eq : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  have hp2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith

private lemma std8_one : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 1 =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [show (1 : ZMod 8) = ((1 : ℤ) : ZMod 8) by norm_num, ZMod.stdAddChar_coe]
  norm_num only [Int.cast_one, Int.cast_ofNat]
  have ha : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / (8 : ℂ) =
      ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ha, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

private lemma std8_nat (j : ℕ) :
    (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) (j : ZMod 8) =
      (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) ^ j := by
  rw [show (j : ZMod 8) = j • (1 : ZMod 8) by simp,
    AddChar.map_nsmul_eq_pow, std8_one]

private lemma std8_0 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 0 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^0 := by
  simpa using std8_nat 0
private lemma std8_1 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 1 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^1 := by
  simpa using std8_nat 1
private lemma std8_2 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 2 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^2 := by
  simpa using std8_nat 2
private lemma std8_3 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 3 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^3 := by
  simpa using std8_nat 3
private lemma std8_4 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 4 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^4 := by
  simpa using std8_nat 4
private lemma std8_5 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 5 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^5 := by
  simpa using std8_nat 5
private lemma std8_6 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 6 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^6 := by
  simpa using std8_nat 6
private lemma std8_7 : (ZMod.stdAddChar : AddChar (ZMod 8) ℂ) 7 =
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)^7 := by
  simpa using std8_nat 7

private lemma chi8_eval (j : Fin 8) :
    chi8C (j.val : ZMod 8) = ((ZMod.χ₈ (j.val : ZMod 8) : ℤ) : ℂ) := rfl
private lemma chi8'_eval (j : Fin 8) :
    chi8'C (j.val : ZMod 8) = ((ZMod.χ₈' (j.val : ZMod 8) : ℤ) : ℂ) := rfl

private lemma sum_zmod8_explicit (f : ZMod 8 → ℂ) :
    (∑ x : ZMod 8, f x) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have hu : (Finset.univ : Finset (ZMod 8)) = {0,1,2,3,4,5,6,7} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide : (0 : ZMod 8) ∉ {(1 : ZMod 8),(2 : ZMod 8),(3 : ZMod 8),(4 : ZMod 8),(5 : ZMod 8),(6 : ZMod 8),(7 : ZMod 8)})]
  rw [Finset.sum_insert (by decide : (1 : ZMod 8) ∉ {(2 : ZMod 8),(3 : ZMod 8),(4 : ZMod 8),(5 : ZMod 8),(6 : ZMod 8),(7 : ZMod 8)})]
  rw [Finset.sum_insert (by decide : (2 : ZMod 8) ∉ {(3 : ZMod 8),(4 : ZMod 8),(5 : ZMod 8),(6 : ZMod 8),(7 : ZMod 8)})]
  rw [Finset.sum_insert (by decide : (3 : ZMod 8) ∉ {(4 : ZMod 8),(5 : ZMod 8),(6 : ZMod 8),(7 : ZMod 8)})]
  rw [Finset.sum_insert (by decide : (4 : ZMod 8) ∉ {(5 : ZMod 8),(6 : ZMod 8),(7 : ZMod 8)})]
  rw [Finset.sum_insert (by decide : (5 : ZMod 8) ∉ {(6 : ZMod 8),(7 : ZMod 8)})]
  rw [Finset.sum_insert (by decide : (6 : ZMod 8) ∉ {(7 : ZMod 8)})]
  rw [Finset.sum_singleton]
  ring

private lemma chi8C_0 : chi8C (0 : ZMod 8) = 0 := by
  have h : ZMod.χ₈ (0 : ZMod 8) = 0 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_1 : chi8C (1 : ZMod 8) = 1 := by
  have h : ZMod.χ₈ (1 : ZMod 8) = 1 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_2 : chi8C (2 : ZMod 8) = 0 := by
  have h : ZMod.χ₈ (2 : ZMod 8) = 0 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_3 : chi8C (3 : ZMod 8) = -1 := by
  have h : ZMod.χ₈ (3 : ZMod 8) = -1 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_4 : chi8C (4 : ZMod 8) = 0 := by
  have h : ZMod.χ₈ (4 : ZMod 8) = 0 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_5 : chi8C (5 : ZMod 8) = -1 := by
  have h : ZMod.χ₈ (5 : ZMod 8) = -1 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_6 : chi8C (6 : ZMod 8) = 0 := by
  have h : ZMod.χ₈ (6 : ZMod 8) = 0 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8C_7 : chi8C (7 : ZMod 8) = 1 := by
  have h : ZMod.χ₈ (7 : ZMod 8) = 1 := by decide
  simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_0 : chi8'C (0 : ZMod 8) = 0 := by
  have h : ZMod.χ₈' (0 : ZMod 8) = 0 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_1 : chi8'C (1 : ZMod 8) = 1 := by
  have h : ZMod.χ₈' (1 : ZMod 8) = 1 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_2 : chi8'C (2 : ZMod 8) = 0 := by
  have h : ZMod.χ₈' (2 : ZMod 8) = 0 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_3 : chi8'C (3 : ZMod 8) = 1 := by
  have h : ZMod.χ₈' (3 : ZMod 8) = 1 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_4 : chi8'C (4 : ZMod 8) = 0 := by
  have h : ZMod.χ₈' (4 : ZMod 8) = 0 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_5 : chi8'C (5 : ZMod 8) = -1 := by
  have h : ZMod.χ₈' (5 : ZMod 8) = -1 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_6 : chi8'C (6 : ZMod 8) = 0 := by
  have h : ZMod.χ₈' (6 : ZMod 8) = 0 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

private lemma chi8'C_7 : chi8'C (7 : ZMod 8) = -1 := by
  have h : ZMod.χ₈' (7 : ZMod 8) = -1 := by decide
  simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) h

lemma chi8C_rootNumber_one : chi8C.rootNumber = 1 := by
  rw [DirichletCharacter.rootNumber]
  have he : chi8C.Even := by
    change chi8C (-1) = 1
    simpa using chi8C_7
  rw [if_pos he, pow_zero, div_one]
  unfold gaussSum
  rw [sum_zmod8_explicit]
  rw [chi8C_0, chi8C_1, chi8C_2, chi8C_3, chi8C_4, chi8C_5, chi8C_6, chi8C_7]
  rw [std8_0, std8_1, std8_2, std8_3, std8_4, std8_5, std8_6, std8_7, cpow_half_nat_eq_sqrt]
  norm_num only [Nat.cast_ofNat]
  rw [show ((Real.sqrt (8 : ℝ) : ℝ) : ℂ) = ((2 * Real.sqrt 2 : ℝ) : ℂ) by rw [sqrt8_eq]]
  norm_num
  have hs : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  field_simp
  ring_nf
  have hs4 : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 = 4 := by
    calc
      _ = ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs]; norm_num
  have hs6 : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 6 = 8 := by
    calc
      _ = ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) ^ 3 := by ring
      _ = 8 := by rw [hs]; norm_num
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show Complex.I^3 = Complex.I^2*Complex.I by ring, hI2, neg_mul, one_mul]
  have hI4 : Complex.I ^ 4 = 1 := by
    calc _ = (Complex.I * Complex.I) * (Complex.I * Complex.I) := by ring
         _ = 1 := by rw [Complex.I_mul_I]; norm_num
  have hI5 : Complex.I ^ 5 = Complex.I := by rw [show Complex.I^5 = Complex.I^4*Complex.I by ring, hI4, one_mul]
  have hI6 : Complex.I ^ 6 = -1 := by rw [show Complex.I^6 = Complex.I^4*(Complex.I*Complex.I) by ring, hI4, one_mul, Complex.I_mul_I]
  have hI7 : Complex.I ^ 7 = -Complex.I := by rw [show Complex.I^7 = Complex.I^6*Complex.I by ring, hI6, neg_mul, one_mul]
  have hI8 : Complex.I ^ 8 = 1 := by rw [show Complex.I^8 = Complex.I^4*Complex.I^4 by ring, hI4, one_mul]
  simp only [hs, hs4, hs6, hI2, hI3, hI4, hI5, hI6, hI7, hI8]
  ring

lemma chi8'C_rootNumber_one : chi8'C.rootNumber = 1 := by
  rw [DirichletCharacter.rootNumber]
  have ho : chi8'C.Odd := by
    change chi8'C (-1) = -1
    simpa using chi8'C_7
  rw [if_neg ho.not_even, pow_one]
  unfold gaussSum
  rw [sum_zmod8_explicit]
  rw [chi8'C_0, chi8'C_1, chi8'C_2, chi8'C_3, chi8'C_4, chi8'C_5, chi8'C_6, chi8'C_7]
  rw [std8_0, std8_1, std8_2, std8_3, std8_4, std8_5, std8_6, std8_7, cpow_half_nat_eq_sqrt]
  norm_num only [Nat.cast_ofNat]
  rw [show ((Real.sqrt (8 : ℝ) : ℝ) : ℂ) = ((2 * Real.sqrt 2 : ℝ) : ℂ) by rw [sqrt8_eq]]
  norm_num
  have hs : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  field_simp [Complex.I_ne_zero]
  ring_nf
  have hs4 : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 = 4 := by
    calc
      _ = ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs]; norm_num
  have hs6 : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 6 = 8 := by
    calc
      _ = ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) ^ 3 := by ring
      _ = 8 := by rw [hs]; norm_num
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show Complex.I^3 = Complex.I^2*Complex.I by ring, hI2, neg_mul, one_mul]
  have hI4 : Complex.I ^ 4 = 1 := by
    calc _ = (Complex.I * Complex.I) * (Complex.I * Complex.I) := by ring
         _ = 1 := by rw [Complex.I_mul_I]; norm_num
  have hI5 : Complex.I ^ 5 = Complex.I := by rw [show Complex.I^5 = Complex.I^4*Complex.I by ring, hI4, one_mul]
  have hI6 : Complex.I ^ 6 = -1 := by rw [show Complex.I^6 = Complex.I^4*(Complex.I*Complex.I) by ring, hI4, one_mul, Complex.I_mul_I]
  have hI7 : Complex.I ^ 7 = -Complex.I := by rw [show Complex.I^7 = Complex.I^6*Complex.I by ring, hI6, neg_mul, one_mul]
  have hI8 : Complex.I ^ 8 = 1 := by rw [show Complex.I^8 = Complex.I^4*Complex.I^4 by ring, hI4, one_mul]
  simp only [hs, hs4, hs6, hI2, hI3, hI4, hI5, hI6, hI7, hI8]
  ring
