import FormalConjectures.Util.ProblemImports

noncomputable section
open Finset Complex Polynomial Matrix
namespace QuadraticBias

private def diagP : ℂ[X] := C (1 / 2 - I) * X + C (1 / 2 + I) * X ^ 3
private def diagQ : ℂ[X] := C (4 / 3 - I / 6) * X + C (-1 / 3 + I / 6) * X ^ 3

private lemma diag_identity :
    diagQ.comp diagP - X = (X ^ 4 - 1) *
      (C (1 / 2 - 7 * I / 48) * X ^ 5 +
       C (-5 / 4 - 15 * I / 16) * X ^ 3 + C (1 / 2 + 17 * I / 12) * X) := by
  apply Polynomial.funext
  intro z
  simp [diagP, diagQ, eval_comp]
  ring_nf
  simp [I_sq, I_pow_three]
  <;> ring

private lemma diag_recover {A : Type*} [Ring A] [Algebra ℂ A] (a : A) (ha : a ^ 4 = 1) :
    aeval (aeval a diagP) diagQ = a := by
  rw [← aeval_comp, ← sub_eq_zero]
  conv_lhs => rhs; rw [← aeval_X (R := ℂ) a]
  rw [← map_sub, diag_identity, map_mul]
  simp [ha]

private lemma fourth_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : Aᴴ * A = 1) (h4 : A ^ 4 = 1) :
    ∃ (U : unitaryGroup n ℂ) (d : n → ℂ),
      A = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) (diagonal d) ∧
      ∀ i, d i ^ 4 = 1 := by
  have hstar : Aᴴ = A ^ 3 := by
    calc
      Aᴴ = Aᴴ * A ^ 4 := by rw [h4, mul_one]
      _ = (Aᴴ * A) * A ^ 3 := by rw [pow_succ', mul_assoc]
      _ = A ^ 3 := by rw [hA, one_mul]
  let H := aeval A diagP
  have hHdef : H = (1 / 2 - I : ℂ) • A + (1 / 2 + I : ℂ) • Aᴴ := by
    simp [H, diagP, hstar, Algebra.smul_def]
  have hH : H.IsHermitian := by
    rw [IsHermitian, hHdef, conjTranspose_add, conjTranspose_smul,
      conjTranspose_smul, conjTranspose_conjTranspose]
    simp only [star_sub, star_add, star_div₀, star_one, star_ofNat, star_def, conj_I]
    module
  let U := hH.eigenvectorUnitary
  let d : n → ℂ := fun i => aeval (hH.eigenvalues i : ℂ) diagQ
  have hh : A = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) (diagonal d) := by
    have hr := diag_recover A h4
    change aeval H diagQ = A at hr
    rw [← hr, hH.spectral_theorem, aeval_algHom_apply]
    congr 1
    simp only [d, diagQ, map_add, map_mul, aeval_C, aeval_X, map_pow,
      Matrix.diagonal_pow]
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  refine ⟨U, d, hh, ?_⟩
  rw [hh, ← map_pow, ← map_one (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U)] at h4
  have hd := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U).injective h4
  intro i
  have hi := congrArg (fun M : Matrix n n ℂ => M i i) hd
  simpa [Matrix.diagonal_pow] using hi

private lemma fourth_eq {z : ℂ} (hz : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = I ∨ z = -I := by
  have hz' : (z ^ 2) ^ 2 = (1 : ℂ) ^ 2 := by simpa [← pow_mul] using hz
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hz' with h | h
  · rcases eq_or_eq_neg_of_sq_eq_sq z 1 (by simpa using h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hh : z ^ 2 = I ^ 2 := by simpa using h
    exact Or.inr (Or.inr (eq_or_eq_neg_of_sq_eq_sq _ _ hh))

private lemma trace_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private lemma det_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) A).det = A.det := by
  rw [Unitary.conjStarAlgAut_apply, det_mul, det_mul, mul_right_comm,
    ← det_mul, (Matrix.mul_eq_one_comm.mp (Unitary.coe_star_mul_self U)), det_one, one_mul]

private lemma fourth_trace_data {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : Aᴴ * A = 1) (h4 : A ^ 4 = 1) :
    ∃ a b c d : ℕ,
      Fintype.card n = a + b + c + d ∧
      A.trace = (a : ℂ) - b + ((c : ℂ) - d) * I ∧
      (A ^ 2).trace = (a : ℂ) + b - c - d ∧
      A.det = I ^ (2 * b + c + 3 * d) := by
  classical
  obtain ⟨U, v, hv, hpow⟩ := fourth_diagonal A hA h4
  have hcases (i : n) := fourth_eq (hpow i)
  let a := #{i | v i = 1}
  let b := #{i | v i = -1}
  let c := #{i | v i = I}
  let d := #{i | v i = -I}
  have hcard : Fintype.card n = a + b + c + d := by
    dsimp [a, b, c, d]
    simp only [card_filter, ← sum_add_distrib]
    rw [← card_univ]
    calc
      univ.card = ∑ i : n, (1 : ℕ) := by simp
      _ = _ := by
        apply sum_congr rfl
        intro i _
        rcases hcases i with h | h | h | h <;>
          norm_num [h, Complex.ext_iff]
  have hsum : ∑ i, v i = (a : ℂ) - b + ((c : ℂ) - d) * I := by
    have hv' (i : n) : v i =
        (if v i = 1 then 1 else 0) - (if v i = -1 then 1 else 0) +
        ((if v i = I then 1 else 0) - (if v i = -I then 1 else 0)) * I := by
      rcases hcases i with h | h | h | h <;> norm_num [h, Complex.ext_iff]
    conv_lhs => arg 2; ext i; rw [hv' i]
    simp only [sum_add_distrib, sum_sub_distrib, ← sum_mul, sum_boole]
    rfl
  have hsqsum : ∑ i, v i ^ 2 = (a : ℂ) + b - c - d := by
    have hv' (i : n) : v i ^ 2 =
        (if v i = 1 then 1 else 0) + (if v i = -1 then 1 else 0) -
        (if v i = I then 1 else 0) - (if v i = -I then 1 else 0) := by
      rcases hcases i with h | h | h | h <;> norm_num [h, Complex.ext_iff]
    conv_lhs => arg 2; ext i; rw [hv' i]
    simp only [sum_add_distrib, sum_sub_distrib, sum_boole]
    rfl
  have hprod : ∏ i, v i = I ^ (2 * b + c + 3 * d) := by
    have hv' (i : n) : v i =
        (if v i = -1 then -1 else 1) * (if v i = I then I else 1) *
        (if v i = -I then -I else 1) := by
      rcases hcases i with h | h | h | h <;> norm_num [h, Complex.ext_iff]
    conv_lhs => arg 2; ext i; rw [hv' i]
    simp only [prod_mul_distrib, prod_ite, prod_const, one_pow, mul_one]
    change (-1 : ℂ) ^ b * I ^ c * (-I) ^ d = _
    rw [← I_sq, ← I_pow_three, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  refine ⟨a, b, c, d, hcard, ?_, ?_, ?_⟩
  · rw [hv, trace_unitary_conj, trace_diagonal]
    exact hsum
  · rw [hv, ← map_pow, trace_unitary_conj, diagonal_pow, trace_diagonal]
    exact hsqsum
  · rw [hv, det_unitary_conj, det_diagonal]
    exact hprod

private lemma I_pow_eq_mod {a b : ℕ} (h : I ^ a = I ^ b) : a % 4 = b % 4 := by
  rw [I_pow_eq_pow_mod a, I_pow_eq_pow_mod b] at h
  have ha := Nat.mod_lt a (by decide : 0 < 4)
  have hb := Nat.mod_lt b (by decide : 0 < 4)
  interval_cases a % 4 <;> interval_cases b % 4 <;> norm_num [Complex.ext_iff] at *

private lemma fourth_count_sign (a b c d m : ℕ)
    (hcard : 2 * m + 1 = a + b + c + d)
    (hsq : a + b = c + d + 1)
    (hnorm : ((a : ℤ) - b) ^ 2 + ((c : ℤ) - d) ^ 2 = 1)
    (hdet : (2 * b + c + 3 * d) % 4 = ((2 * m + 1) * m) % 4) :
    (a = b + 1 ∧ c = d ∧ m % 2 = 0) ∨ (a = b ∧ c = d + 1 ∧ m % 2 = 1) := by
  let x : ℤ := (a : ℤ) - b
  let y : ℤ := (c : ℤ) - d
  have hxy : x ^ 2 + y ^ 2 = 1 := hnorm
  have hxlo : -1 ≤ x := by nlinarith [sq_nonneg y]
  have hxhi : x ≤ 1 := by nlinarith [sq_nonneg y]
  have hylo : -1 ≤ y := by nlinarith [sq_nonneg x]
  have hyhi : y ≤ 1 := by nlinarith [sq_nonneg x]
  have hxdef : x = (a : ℤ) - b := rfl
  have hydef : y = (c : ℤ) - d := rfl
  rw [Nat.mul_mod (2 * m + 1), Nat.add_mod (2 * m) 1 4, Nat.mul_mod 2 m 4] at hdet
  have hm := Nat.mod_lt m (by decide : 0 < 4)
  interval_cases x <;> interval_cases y <;> norm_num at hxy <;>
    interval_cases hm4 : m % 4 <;> norm_num at hdet <;> omega

private lemma fourth_trace_sign {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (m : ℕ) (hn : Fintype.card n = 2 * m + 1)
    (hA : Aᴴ * A = 1) (h4 : A ^ 4 = 1)
    (hsq : (A ^ 2).trace = 1) (hnorm : ‖A.trace‖ = 1)
    (hdet : A.det = I ^ ((2 * m + 1) * m)) :
    A.trace = if m % 2 = 0 then 1 else I := by
  obtain ⟨a, b, c, d, hcard, htr, htrsq, hprod⟩ := fourth_trace_data A hA h4
  rw [hn] at hcard
  have hsqr : (a : ℝ) + b - c - d = 1 := by
    have h := congrArg Complex.re (htrsq.symm.trans hsq)
    simpa using h
  have hsqi : a + b = c + d + 1 := by
    exact_mod_cast (show (a : ℝ) + b = c + d + 1 by linarith)
  have hnormR : ((a : ℝ) - b) ^ 2 + ((c : ℝ) - d) ^ 2 = 1 := by
    have h := normSq_eq_norm_sq A.trace
    rw [hnorm, htr] at h
    simpa [normSq_apply, pow_two] using h
  have hnormZ : ((a : ℤ) - b) ^ 2 + ((c : ℤ) - d) ^ 2 = 1 := by
    exact_mod_cast hnormR
  have hdetmod := I_pow_eq_mod (hprod.symm.trans hdet)
  rcases fourth_count_sign a b c d m hcard hsqi hnormZ hdetmod with
    ⟨rfl, rfl, hm⟩ | ⟨rfl, rfl, hm⟩
  · simp [htr, hm]
  · simp [htr, hm]

section GaussBasic
variable {N : ℕ} [NeZero N]

/-- The quadratic exponential sum, without a multiplicative character. -/
def QG (N : ℕ) [NeZero N] (a : ZMod N) : ℂ :=
  ∑ x : ZMod N, ZMod.stdAddChar (a * x ^ 2)

private lemma char_conj (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

private lemma char_norm (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := Circle.norm_coe _

private lemma char_sum (a : ZMod N) :
    ∑ x : ZMod N, ZMod.stdAddChar (a * x) = if a = 0 then (N : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)

private def FM (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun i j => ZMod.stdAddChar (i * j)

private def UFM (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  ((Real.sqrt N : ℂ)⁻¹) • FM N

private lemma sqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos N)
private lemma sqrtN_ne : (Real.sqrt N : ℂ) ≠ 0 := by
  exact_mod_cast (sqrtN_pos (N := N)).ne'
private lemma sqrtN_sq : (Real.sqrt N : ℂ) ^ 2 = N := by
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N)

private lemma FM_star_mul : (FM N)ᴴ * FM N = (N : ℂ) • (1 : Matrix (ZMod N) (ZMod N) ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, FM, char_conj,
    ← AddChar.map_add_eq_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  have h (k : ZMod N) : -(k * i) + k * j = (j - i) * k := by ring
  simp_rw [h]
  rw [char_sum]
  by_cases hij : i = j
  · simp [hij]
  · simp [sub_ne_zero.mpr (Ne.symm hij), hij]

private lemma UFM_star_mul : (UFM N)ᴴ * UFM N = 1 := by
  rw [UFM, Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
    FM_star_mul, smul_smul]
  have hc : star ((Real.sqrt N : ℂ)⁻¹) * (Real.sqrt N : ℂ)⁻¹ * (N : ℂ) = 1 := by
    simp only [star_def, map_inv₀, conj_ofReal]
    rw [← sqrtN_sq, pow_two]
    field_simp [sqrtN_ne]
    exact div_self sqrtN_ne
  rw [hc, one_smul]

private lemma UFM_sq_apply (i j : ZMod N) :
    (UFM N ^ 2) i j = if j = -i then 1 else 0 := by
  rw [pow_two, UFM, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.smul_apply]
  simp only [Matrix.mul_apply, FM, smul_eq_mul, ← AddChar.map_add_eq_mul]
  have h (k : ZMod N) : i * k + k * j = (i + j) * k := by ring
  simp_rw [h]
  rw [char_sum]
  have heq : i + j = 0 ↔ j = -i := by constructor <;> intro h <;> linear_combination h
  simp only [heq]
  split_ifs
  · rw [← sqrtN_sq, pow_two]
    field_simp [sqrtN_ne]
    exact div_self sqrtN_ne
  · simp

private lemma UFM_four : UFM N ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by decide, pow_mul, pow_two]
  ext i j
  simp only [Matrix.mul_apply, UFM_sq_apply, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true, neg_neg]
  simp only [eq_comm]

private lemma unit_two_of_odd (hN : Odd N) : IsUnit (2 : ZMod N) := by
  rw [← Nat.cast_two, ZMod.isUnit_iff_coprime]
  exact Nat.coprime_two_left.mpr hN

private lemma neg_self_iff (hN : Odd N) (x : ZMod N) : x = -x ↔ x = 0 := by
  constructor
  · intro hx
    have h2 : (2 : ZMod N) * x = 0 := by linear_combination hx
    exact (unit_two_of_odd hN).mul_right_cancel (by simpa [mul_comm] using h2)
  · rintro rfl; simp

private lemma UFM_trace_sq (hN : Odd N) : (UFM N ^ 2).trace = 1 := by
  simp [Matrix.trace, UFM_sq_apply, neg_self_iff hN]

private lemma UFM_trace : (UFM N).trace = QG N 1 / (Real.sqrt N : ℂ) := by
  simp [UFM, Matrix.trace, Matrix.smul_apply, FM, QG, pow_two, div_eq_mul_inv,
    mul_comm, mul_sum]

private def sumDiffEquiv (hN : Odd N) : (ZMod N × ZMod N) ≃ (ZMod N × ZMod N) := by
  let u : ZMod N := ((unit_two_of_odd hN).unit⁻¹).val
  have hu : (2 : ZMod N) * u = 1 := by
    simpa only [u, IsUnit.unit_spec] using
      (unit_two_of_odd hN).unit.val_inv
  refine {
    toFun := fun p => (p.1 - p.2, p.1 + p.2)
    invFun := fun p => ((p.1 + p.2) * u, (p.2 - p.1) * u)
    left_inv := ?_
    right_inv := ?_ }
  · intro p
    ext <;> dsimp
    · linear_combination p.1 * hu
    · linear_combination p.2 * hu
  · intro p
    ext <;> dsimp
    · linear_combination p.1 * hu
    · linear_combination p.2 * hu

private lemma QG_mul_star (hN : Odd N) : QG N 1 * star (QG N 1) = (N : ℂ) := by
  simp only [QG, one_mul, star_sum, char_conj, sum_mul_sum, ← AddChar.map_add_eq_mul]
  change (∑ x : ZMod N, ∑ y : ZMod N, (fun p : ZMod N × ZMod N =>
    ZMod.stdAddChar (p.1 ^ 2 + -(p.2 ^ 2))) (x, y)) = _
  rw [← Fintype.sum_prod_type (fun p : ZMod N × ZMod N => ZMod.stdAddChar (p.1 ^ 2 + -(p.2 ^ 2)))]
  calc
    (∑ p : ZMod N × ZMod N, ZMod.stdAddChar (p.1 ^ 2 + -(p.2 ^ 2))) =
        ∑ p : ZMod N × ZMod N, ZMod.stdAddChar (p.1 * p.2) := by
      apply Fintype.sum_equiv (sumDiffEquiv hN)
      intro p
      congr 1
      change p.1 ^ 2 + -(p.2 ^ 2) = (p.1 - p.2) * (p.1 + p.2)
      ring
    _ = (N : ℂ) := by
      rw [Fintype.sum_prod_type]
      simp [char_sum]

lemma QG_norm (hN : Odd N) : ‖QG N 1‖ = Real.sqrt N := by
  have h := QG_mul_star hN
  rw [star_def, Complex.mul_conj] at h
  have hs : ‖QG N 1‖ ^ 2 = (N : ℝ) := by
    rw [← normSq_eq_norm_sq]
    exact_mod_cast h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), norm_nonneg (QG N 1), Real.sqrt_nonneg (N : ℝ)]

private lemma UFM_trace_norm (hN : Odd N) : ‖(UFM N).trace‖ = 1 := by
  rw [UFM_trace, norm_div, QG_norm hN, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_self (sqrtN_pos (N := N)).ne']

private lemma finEquiv_nat (i : Fin N) : ZMod.finEquiv N i = (i.val : ZMod N) := by
  have hv : (ZMod.finEquiv N i).val = i.val := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  rw [← hv, ZMod.natCast_zmod_val]

lemma char_nat (a : ℕ) :
    ZMod.stdAddChar (a : ZMod N) = exp (2 * Real.pi * I * (a : ℂ) / N) := by
  simpa using ZMod.stdAddChar_coe (N := N) (a : ℤ)

private lemma FM_vandermonde :
    (FM N).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) =
      vandermonde (fun i : Fin N => ZMod.stdAddChar (i.val : ZMod N)) := by
  ext i j
  simp only [Matrix.submatrix_apply, FM, finEquiv_nat, Matrix.vandermonde_apply]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]

private lemma char_diff (i j : Fin N) :
    ZMod.stdAddChar (j.val : ZMod N) - ZMod.stdAddChar (i.val : ZMod N) =
      I * exp (Real.pi * I * ((i : ℂ) + j) / N) *
        ((2 * Real.sin (Real.pi * ((j : ℝ) - i) / N) : ℝ) : ℂ) := by
  rw [char_nat, char_nat]
  push_cast
  rw [Complex.two_sin]
  simp only [mul_sub, sub_mul, ← exp_add]
  have h1 : Real.pi * I * ((i : ℂ) + j) / N +
      -(Real.pi * ((j : ℂ) - i) / N) * I = 2 * Real.pi * I * (i : ℂ) / N := by ring
  have h2 : Real.pi * I * ((i : ℂ) + j) / N +
      Real.pi * ((j : ℂ) - i) / N * I = 2 * Real.pi * I * (j : ℂ) / N := by ring
  calc
    exp (2 * Real.pi * I * (j : ℂ) / N) - exp (2 * Real.pi * I * (i : ℂ) / N) =
      -(exp (2 * Real.pi * I * (i : ℂ) / N) - exp (2 * Real.pi * I * (j : ℂ) / N)) := by ring
    _ = _ := by
      rw [← h1, ← h2, exp_add, exp_add]
      ring_nf
      simp [I_sq]
      <;> ring

private lemma sin_factor_pos {i j : Fin N} (hij : j ∈ Ioi i) :
    0 < 2 * Real.sin (Real.pi * ((j : ℝ) - i) / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hj : (j : ℝ) < N := by exact_mod_cast j.isLt
  have hij' : (i : ℝ) < j := by exact_mod_cast (Finset.mem_Ioi.mp hij)
  apply mul_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr hij')) hN
  · apply (div_lt_iff₀ hN).2
    nlinarith [Real.pi_pos]

private lemma pair_card (m : ℕ) (hn : N = 2 * m + 1) :
    ∑ i : Fin N, (Ioi i).card = N * m := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range, sum_range_reflect (fun i : ℕ => i) N]
  have h := sum_range_id_mul_two N
  rw [hn] at h ⊢
  simp only [Nat.add_sub_cancel] at h
  nlinarith

private lemma pair_sum (m : ℕ) (hn : N = 2 * m + 1) :
    (∑ i : Fin N, ∑ j ∈ Ioi i, ((i : ℝ) + j)) = 2 * N * (m : ℝ) ^ 2 := by
  have hs : (∑ i : Fin N, (i : ℝ)) * 2 = (N : ℝ) * (N - 1) := by
    have h := sum_range_id_mul_two N
    have hN : 1 ≤ N := NeZero.one_le
    have h' : (∑ i ∈ range N, (i : ℝ)) * 2 = (N : ℝ) * (N - 1) := by
      have h0 := congrArg (fun x : ℕ => (x : ℝ)) h
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hN, Nat.cast_one, Nat.cast_sum] using h0
    simpa only [Fin.sum_univ_eq_sum_range] using h'
  have hswap : (∑ i : Fin N, ∑ j ∈ Ioi i, (j : ℝ)) =
      ∑ j : Fin N, ∑ i ∈ Iio j, (j : ℝ) := by
    apply sum_comm'
    intro i j
    simp
  simp_rw [sum_add_distrib]
  rw [hswap]
  simp only [sum_const, nsmul_eq_mul, Fin.card_Ioi, Fin.card_Iio, ← sum_add_distrib]
  calc
    (∑ i : Fin N, (((N - 1 - i.val : ℕ) : ℝ) * i + (i : ℝ) * i)) =
        ∑ i : Fin N, ((N : ℝ) - 1) * i := by
      apply sum_congr rfl
      intro i _
      rw [Nat.cast_sub (by omega : i.val ≤ N - 1), Nat.cast_sub (NeZero.one_le : 1 ≤ N)]
      push_cast
      ring
    _ = ((N : ℝ) - 1) * ∑ i : Fin N, (i : ℝ) := (mul_sum ..).symm
    _ = 2 * N * (m : ℝ) ^ 2 := by
      have hn' : (N : ℝ) = 2 * m + 1 := by exact_mod_cast hn
      rw [hn'] at hs ⊢
      nlinarith

private lemma FM_det_phase (m : ℕ) (hn : N = 2 * m + 1) :
    ∃ r : ℝ, 0 < r ∧ (FM N).det = I ^ (N * m) * (r : ℂ) := by
  let r : ℝ := ∏ i : Fin N, ∏ j ∈ Ioi i,
    2 * Real.sin (Real.pi * ((j : ℝ) - i) / N)
  have hr : 0 < r := by
    apply prod_pos
    intro i _
    exact prod_pos fun j hj => sin_factor_pos hj
  have he : (∏ i : Fin N, ∏ j ∈ Ioi i,
      exp (Real.pi * I * ((i : ℂ) + j) / N)) = 1 := by
    simp_rw [← Complex.exp_sum]
    have hs : (∑ i : Fin N, ∑ j ∈ Ioi i, ((i : ℂ) + j)) =
        2 * N * (m : ℂ) ^ 2 := by
      exact_mod_cast pair_sum m hn
    have hx (i j : Fin N) : Real.pi * I * ((i : ℂ) + j) / N =
        (Real.pi * I / N) * ((i : ℂ) + j) := by ring
    simp_rw [hx, ← mul_sum]
    rw [hs]
    have hx' : Real.pi * I / N * (2 * N * (m : ℂ) ^ 2) =
        (m ^ 2 : ℕ) * (2 * Real.pi * I) := by
      push_cast
      field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℂ) ≠ 0)]
      <;> ring
    rw [hx']
    exact Complex.exp_nat_mul_two_pi_mul_I _
  refine ⟨r, hr, ?_⟩
  rw [← Matrix.det_submatrix_equiv_self (ZMod.finEquiv N).toEquiv (FM N)]
  change ((FM N).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N)).det = _
  rw [FM_vandermonde, Matrix.det_vandermonde]
  simp_rw [char_diff, prod_mul_distrib, prod_const]
  rw [prod_pow_eq_pow_sum, pair_card m hn, he, mul_one]
  congr 1
  simp [r]

private lemma UFM_det (m : ℕ) (hn : N = 2 * m + 1) :
    (UFM N).det = I ^ (N * m) := by
  obtain ⟨r, hr, hFM⟩ := FM_det_phase m hn
  let t : ℝ := (Real.sqrt N)⁻¹ ^ N * r
  have ht : 0 < t := mul_pos (pow_pos (inv_pos.mpr sqrtN_pos) _) hr
  have hd : (UFM N).det = I ^ (N * m) * (t : ℂ) := by
    rw [UFM, Matrix.det_smul, ZMod.card, hFM]
    dsimp [t]
    push_cast
    ring
  have hunit := congrArg (fun A : Matrix (ZMod N) (ZMod N) ℂ => ‖A.det‖) (UFM_star_mul (N := N))
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one,
    norm_one] at hunit
  have hdnorm : ‖(UFM N).det‖ = 1 := by nlinarith [norm_nonneg (UFM N).det]
  rw [hd, norm_mul, norm_pow, norm_I, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht] at hdnorm
  simpa [hdnorm] using hd

/-- The sign, and not just the square, of the odd quadratic Gauss sum. -/
lemma QG_one_odd (hN : Odd N) :
    QG N 1 = (if N % 4 = 1 then 1 else I) * (Real.sqrt N : ℂ) := by
  let m := N / 2
  have hn : N = 2 * m + 1 := by
    have := Nat.odd_iff.mp hN
    dsimp [m]
    omega
  have h := fourth_trace_sign (UFM N) m (by simpa [ZMod.card] using hn)
    UFM_star_mul UFM_four (UFM_trace_sq hN) (UFM_trace_norm hN)
    (by simpa only [← hn] using UFM_det m hn)
  rw [UFM_trace] at h
  have hi : m % 2 = 0 ↔ N % 4 = 1 := by omega
  simpa only [hi] using (div_eq_iff sqrtN_ne).mp h

/-- The quadratic character defined by the sign of multiplication on the residue ring. -/
def signChar (N : ℕ) [NeZero N] : MulChar (ZMod N) ℤ :=
  MulChar.ofUnitHom {
    toFun := fun u => Equiv.Perm.sign u.mulLeft
    map_one' := by
      have h : (1 : (ZMod N)ˣ).mulLeft = 1 := by ext x; simp [Units.mulLeft]
      rw [h, map_one]
    map_mul' := by
      intro u v
      have h : (u * v).mulLeft = u.mulLeft * v.mulLeft := by
        ext x
        simp [Units.mulLeft, mul_assoc]
      rw [h, map_mul] }

lemma signChar_unit (u : (ZMod N)ˣ) :
    signChar N (u : ZMod N) = (Equiv.Perm.sign u.mulLeft : ℤ) := by
  apply MulChar.ofUnitHom_coe

lemma signChar_quad (a : ZMod N) : signChar N a = 0 ∨ signChar N a = 1 ∨ signChar N a = -1 := by
  by_cases ha : IsUnit a
  · right
    rw [← ha.unit_spec, signChar_unit]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ha.unit.mulLeft) with h | h <;> simp [h]
  · exact Or.inl (MulChar.map_nonunit _ ha)

private def UFA (a : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ :=
  (UFM N).submatrix (fun i => a * i) id

private lemma UFA_apply (a i j : ZMod N) :
    UFA a i j = (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (a * i * j) := rfl

private lemma UFA_star_mul (u : (ZMod N)ˣ) : (UFA (u : ZMod N))ᴴ * UFA u = 1 := by
  rw [← UFM_star_mul (N := N)]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, UFA, Matrix.submatrix_apply,
    id_eq]
  exact Fintype.sum_equiv u.mulLeft _ _ (fun x => rfl)

private lemma UFA_sq_apply (u : (ZMod N)ˣ) (i j : ZMod N) :
    (UFA (u : ZMod N) ^ 2) i j = if j = -i then 1 else 0 := by
  rw [pow_two]
  simp only [Matrix.mul_apply, UFA_apply]
  have heq : (u : ZMod N) * (i + j) = 0 ↔ j = -i := by
    rw [u.isUnit.mul_right_eq_zero]
    constructor <;> intro h <;> linear_combination h
  have hx (k : ZMod N) : (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar ((u : ZMod N) * i * k) *
      ((Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar ((u : ZMod N) * k * j)) =
      (Real.sqrt N : ℂ)⁻¹ ^ 2 * ZMod.stdAddChar ((u : ZMod N) * (i + j) * k) := by
    rw [show (u : ZMod N) * (i + j) * k = (u : ZMod N) * i * k + (u : ZMod N) * k * j by ring,
      AddChar.map_add_eq_mul]
    ring
  simp_rw [hx, ← mul_sum]
  rw [char_sum]
  simp only [heq]
  split_ifs
  · rw [← sqrtN_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ sqrtN_ne)]
  · simp

private lemma UFA_four (u : (ZMod N)ˣ) : UFA (u : ZMod N) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by decide, pow_mul, pow_two]
  ext i j
  simp only [Matrix.mul_apply, UFA_sq_apply, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true, neg_neg]
  simp only [eq_comm]

private lemma UFA_trace_sq (hN : Odd N) (u : (ZMod N)ˣ) :
    (UFA (u : ZMod N) ^ 2).trace = 1 := by
  simp [Matrix.trace, UFA_sq_apply, neg_self_iff hN]

private lemma UFA_trace (a : ZMod N) :
    (UFA a).trace = QG N a / (Real.sqrt N : ℂ) := by
  simp [Matrix.trace, UFA_apply, QG, pow_two, mul_assoc, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_sum]

private lemma QG_mul_star_unit (hN : Odd N) (u : (ZMod N)ˣ) :
    QG N u * star (QG N u) = (N : ℂ) := by
  simp only [QG, star_sum, char_conj, sum_mul_sum, ← AddChar.map_add_eq_mul]
  rw [← Fintype.sum_prod_type (fun p : ZMod N × ZMod N =>
    ZMod.stdAddChar ((u : ZMod N) * p.1 ^ 2 + -((u : ZMod N) * p.2 ^ 2)))]
  calc
    (∑ p : ZMod N × ZMod N, ZMod.stdAddChar ((u : ZMod N) * p.1 ^ 2 + -((u : ZMod N) * p.2 ^ 2))) =
        ∑ p : ZMod N × ZMod N, ZMod.stdAddChar ((u : ZMod N) * p.1 * p.2) := by
      apply Fintype.sum_equiv (sumDiffEquiv hN)
      intro p
      congr 1
      change (u : ZMod N) * p.1 ^ 2 + -((u : ZMod N) * p.2 ^ 2) =
        u * (p.1 - p.2) * (p.1 + p.2)
      ring
    _ = (N : ℂ) := by
      rw [Fintype.sum_prod_type]
      simp [char_sum, u.isUnit.mul_right_eq_zero]

private lemma QG_norm_unit (hN : Odd N) (u : (ZMod N)ˣ) : ‖QG N u‖ = Real.sqrt N := by
  have h := QG_mul_star_unit hN u
  rw [star_def, Complex.mul_conj] at h
  have hs : ‖QG N u‖ ^ 2 = (N : ℝ) := by
    rw [← normSq_eq_norm_sq]
    exact_mod_cast h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), norm_nonneg (QG N u), Real.sqrt_nonneg (N : ℝ)]

lemma QG_unit_odd (hN : Odd N) (u : (ZMod N)ˣ) :
    QG N u = (signChar N u : ℂ) * QG N 1 := by
  let m := N / 2
  have hn : N = 2 * m + 1 := by have := Nat.odd_iff.mp hN; dsimp [m]; omega
  have hi : m % 2 = 0 ↔ N % 4 = 1 := by omega
  have hcard : Fintype.card (ZMod N) = 2 * m + 1 := by simpa [ZMod.card] using hn
  have hnorm : ‖(UFA (u : ZMod N)).trace‖ = 1 := by
    rw [UFA_trace, norm_div, QG_norm_unit hN, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_self (sqrtN_pos (N := N)).ne']
  have hdet : (UFA (u : ZMod N)).det = (signChar N u : ℂ) * I ^ (N * m) := by
    rw [signChar_unit, UFA]
    change ((UFM N).submatrix u.mulLeft id).det = _
    rw [Matrix.det_permute, UFM_det m hn]
  rcases (signChar_quad (u : ZMod N)) with hs | hs | hs
  · have hu : IsUnit (signChar N (u : ZMod N)) := u.isUnit.map (signChar N)
    rw [hs] at hu
    exact (not_isUnit_zero hu).elim
  · have hd : (UFA (u : ZMod N)).det = I ^ ((2 * m + 1) * m) := by
      simpa [hs, ← hn] using hdet
    have h := fourth_trace_sign (UFA (u : ZMod N)) m hcard (UFA_star_mul u)
      (UFA_four u) (UFA_trace_sq hN u) hnorm hd
    rw [UFA_trace] at h
    rw [hs, Int.cast_one, one_mul, QG_one_odd hN]
    simpa only [hi] using (div_eq_iff sqrtN_ne).mp h
  · have hd : (-UFA (u : ZMod N)).det = I ^ ((2 * m + 1) * m) := by
      rw [Matrix.det_neg, ZMod.card, hN.neg_one_pow, hdet, hs]
      simp [← hn]
    have hA : (-UFA (u : ZMod N))ᴴ * -UFA u = 1 := by
      simpa using UFA_star_mul u
    have h4 : (-UFA (u : ZMod N)) ^ 4 = 1 := by
      rw [(by decide : Even 4).neg_pow]
      exact UFA_four u
    have hsq : ((-UFA (u : ZMod N)) ^ 2).trace = 1 := by simpa using UFA_trace_sq hN u
    have hnorm' : ‖(-UFA (u : ZMod N)).trace‖ = 1 := by simpa using hnorm
    have h := fourth_trace_sign (-UFA (u : ZMod N)) m hcard hA h4 hsq hnorm' hd
    rw [Matrix.trace_neg, UFA_trace, ← neg_div] at h
    have hh := (div_eq_iff sqrtN_ne).mp h
    rw [hs, Int.cast_neg, Int.cast_one, neg_one_mul, QG_one_odd hN]
    simpa only [hi, neg_eq_iff_eq_neg] using hh

private lemma upper_triangle_sum (m : ℕ) :
    (∑ j ∈ range (2 * m + 1), if m < j then 2 * m + 1 - j else 0) * 2 = m * (m + 1) := by
  have h : (∑ j ∈ range (2 * m + 1), if m < j then 2 * m + 1 - j else 0) =
      ∑ j ∈ range m, (j + 1) := by
    rw [← sum_range_reflect (fun j => if m < j then 2 * m + 1 - j else 0)]
    calc
      (∑ j ∈ range (2 * m + 1), if m < 2 * m + 1 - 1 - j then
          2 * m + 1 - (2 * m + 1 - 1 - j) else 0) =
        ∑ j ∈ range (2 * m + 1), if j < m then j + 1 else 0 := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        split_ifs <;> omega
      _ = ∑ j ∈ range m, (j + 1) := by
        symm
        calc
          (∑ j ∈ range m, (j + 1)) = ∑ j ∈ range m, if j < m then j + 1 else 0 := by
            apply sum_congr rfl
            intro j hj
            simp [mem_range.mp hj]
          _ = _ := by
            apply sum_subset (range_mono (by omega : m ≤ 2 * m + 1))
            intro j hj hnj
            simp only [mem_range, not_lt] at hnj
            simp [Nat.not_lt.mpr hnj]
  rw [h]
  have ht := sum_range_id_mul_two (m + 1)
  rw [sum_range_succ' (fun j : ℕ => j)] at ht
  simpa [mul_comm] using ht

private lemma triangle_sign (e m : ℕ) (he : e * 2 = m * (m + 1)) :
    (-1 : ℤ) ^ e = ZMod.χ₈ (2 * m + 1 : ℕ) := by
  simp only [neg_one_pow_eq_ite, Nat.even_iff, ZMod.χ₈_nat_eq_if_mod_eight]
  have hm := Nat.mod_lt m (by decide : 0 < 4)
  have hmod := congrArg (fun x : ℕ => x % 4) he
  dsimp only at hmod
  rw [Nat.mul_mod m, Nat.add_mod m 1 4] at hmod
  have hN : (2 * m + 1) % 8 = (2 * (m % 4) + 1) % 8 := by omega
  rw [hN]
  interval_cases hm4 : m % 4 <;> norm_num at hmod ⊢ <;> omega

lemma signChar_two (hN : Odd N) : signChar N 2 = ZMod.χ₈ N := by
  classical
  let m := N / 2
  have hn : N = 2 * m + 1 := by have := Nat.odd_iff.mp hN; dsimp [m]; omega
  let u : (ZMod N)ˣ := (unit_two_of_odd hN).unit
  let σ : Equiv.Perm (Fin N) := (ZMod.finEquiv N).toEquiv.symm.permCongr u.mulLeft
  have hval (i : Fin N) : (σ i).val = (2 * i.val) % N := by
    have h : ZMod.finEquiv N (σ i) = (2 : ZMod N) * ZMod.finEquiv N i := by
      simp [σ, Equiv.permCongr_apply, Units.mulLeft, u]
    have h' := congrArg ZMod.val h
    simp only [finEquiv_nat, ZMod.val_natCast, Nat.mod_eq_of_lt (σ i).isLt] at h'
    have heq : (2 : ZMod N) * (i.val : ZMod N) = ((2 * i.val : ℕ) : ZMod N) := by push_cast; rfl
    simpa only [heq, ZMod.val_natCast] using h'
  have hval' (i : Fin N) : (σ i).val = if i.val ≤ m then 2 * i.val else 2 * i.val - N := by
    rw [hval]
    split_ifs with hi
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega : N ≤ 2 * i.val)]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
  have hinv (i j : Fin N) (hij : i < j) :
      ¬ σ i < σ j ↔ m < j.val ∧ j.val - m ≤ i.val ∧ i.val ≤ m := by
    change ¬ (σ i).val < (σ j).val ↔ _
    rw [hval', hval']
    have hij' : i.val < j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> omega
  have hc (j : Fin N) : #{i ∈ Iio j | ¬ σ i < σ j} = if m < j.val then N - j.val else 0 := by
    by_cases hj : m < j.val
    · let lo : Fin N := ⟨j.val - m, by have := j.isLt; omega⟩
      let hi : Fin N := ⟨m, by omega⟩
      have hs : {i ∈ Iio j | ¬ σ i < σ j} = Icc lo hi := by
        ext i
        simp only [mem_filter, mem_Iio, mem_Icc]
        constructor
        · rintro ⟨hij, hσ⟩
          have h := (hinv i j hij).mp hσ
          exact ⟨h.2.1, h.2.2⟩
        · rintro ⟨hlo, hhi⟩
          have hlo' : j.val - m ≤ i.val := hlo
          have hhi' : i.val ≤ m := hhi
          have hij : i < j := by change i.val < j.val; omega
          exact ⟨hij, (hinv i j hij).mpr ⟨hj, hlo', hhi'⟩⟩
      rw [hs, Fin.card_Icc, if_pos hj]
      dsimp [lo, hi]
      omega
    · rw [if_neg hj]
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hij, hσ⟩ := mem_filter.mp hi
      exact hj ((hinv i j (mem_Iio.mp hij)).mp hσ).1
  have hsign : (σ.sign : ℤ) = (-1 : ℤ) ^
      (∑ j : Fin N, if m < j.val then N - j.val else 0) := by
    rw [Equiv.Perm.sign_eq_prod_prod_Iio]
    norm_cast
    simp only [prod_ite, prod_const, one_pow, one_mul, hc, prod_pow_eq_pow_sum]
    norm_cast
  have he : (∑ j : Fin N, if m < j.val then N - j.val else 0) * 2 = m * (m + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if m < j then N - j else 0), hn]
    exact upper_triangle_sum m
  have hsign' : (σ.sign : ℤ) = ZMod.χ₈ N := by
    rw [hsign, triangle_sign _ m he, hn]
  have hu : (u : ZMod N) = 2 := (unit_two_of_odd hN).unit_spec
  rw [← hu, signChar_unit]
  simpa only [σ, Equiv.Perm.sign_permCongr] using hsign'

end GaussBasic

private lemma sum_range_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n d : ℕ) :
    ∑ k ∈ range (n * d), f k = ∑ y ∈ range d, ∑ x ∈ range n, f (n * y + x) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

private lemma sum_range_stride {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n d : ℕ) :
    ∑ k ∈ range (n * d), f k = ∑ x ∈ range n, ∑ y ∈ range d, f (x + n * y) := by
  rw [sum_range_blocks, sum_comm]
  simp only [add_comm]

/-- An additive character with an integer argument. -/
def EC (n : ℕ) [NeZero n] (x : ℤ) : ℂ := ZMod.stdAddChar (x : ZMod n)

lemma EC_add (n : ℕ) [NeZero n] (x y : ℤ) : EC n (x + y) = EC n x * EC n y := by
  simp only [EC, Int.cast_add, AddChar.map_add_eq_mul]

lemma EC_period (n : ℕ) [NeZero n] (x y : ℤ) : EC n (x + n * y) = EC n x := by
  simp [EC]

lemma EC_sq_period (n : ℕ) [NeZero n] (a x y : ℤ) :
    EC n (a * (x + n * y) ^ 2) = EC n (a * x ^ 2) := by
  simp [EC]

lemma EC_zero (n : ℕ) [NeZero n] : EC n 0 = 1 := by simp [EC]

lemma EC_mul_right (m n : ℕ) [NeZero m] [NeZero n] (x : ℤ) :
    EC (m * n) (m * x) = EC n x := by
  rw [EC, EC, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℂ) ≠ 0)]
  <;> ring

lemma EC_mul_left (m n : ℕ) [NeZero m] [NeZero n] (x : ℤ) :
    EC (m * n) (n * x) = EC m x := by
  simpa only [mul_comm n m] using EC_mul_right n m x

lemma QG_sum_range (n : ℕ) [NeZero n] (a : ℤ) :
    QG n (a : ZMod n) = ∑ k ∈ range n, EC n (a * (k : ℤ) ^ 2) := by
  rw [QG, ← (ZMod.finEquiv n).toEquiv.sum_comp]
  change (∑ i : Fin n, ZMod.stdAddChar ((a : ZMod n) * (ZMod.finEquiv n i) ^ 2)) = _
  simp only [finEquiv_nat, EC, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun k => ZMod.stdAddChar ((a : ZMod n) * (k : ZMod n) ^ 2))]

lemma QG_level_mul (d n : ℕ) [NeZero d] [NeZero n] (a : ℤ) :
    QG (d * n) ((d : ℤ) * a : ℤ) = (d : ℂ) * QG n a := by
  rw [QG_sum_range, QG_sum_range]
  have he (k : ℕ) : EC (d * n) ((d : ℤ) * a * (k : ℤ) ^ 2) = EC n (a * (k : ℤ) ^ 2) := by
    rw [mul_assoc, EC_mul_right]
  simp_rw [he]
  rw [mul_comm d n, sum_range_stride]
  simp only [Nat.cast_add, Nat.cast_mul, EC_sq_period, sum_const, card_range, nsmul_eq_mul]
  exact (mul_sum ..).symm



private lemma EC_CRT_sq (m n : ℕ) [NeZero m] [NeZero n] (a x y : ℤ) :
    EC (m * n) (a * ((n : ℤ) * x + m * y) ^ 2) =
      EC m (a * n * x ^ 2) * EC n (a * m * y ^ 2) := by
  have h : a * ((n : ℤ) * x + m * y) ^ 2 =
      (n : ℤ) * (a * n * x ^ 2) + (m : ℤ) * (a * m * y ^ 2) +
        (m * n : ℕ) * (2 * a * x * y) := by push_cast; ring
  rw [h, EC_period, EC_add, EC_mul_left, EC_mul_right]

lemma QG_CRT (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) (a : ℤ) :
    QG (m * n) a = QG m (a * n : ℤ) * QG n (a * m : ℤ) := by
  let f : ZMod m × ZMod n → ZMod (m * n) :=
    fun p => (n : ZMod (m * n)) * p.1.val + (m : ZMod (m * n)) * p.2.val
  have hM (p : ZMod m × ZMod n) :
      ZMod.castHom (dvd_mul_right m n) (ZMod m) (f p) = (n : ZMod m) * p.1 := by
    simp only [f, map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, zero_add, mul_zero, add_zero, ZMod.natCast_zmod_val]
  have hN (p : ZMod m × ZMod n) :
      ZMod.castHom (dvd_mul_left n m) (ZMod n) (f p) = (m : ZMod n) * p.2 := by
    simp only [f, map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, zero_add, mul_zero, add_zero, ZMod.natCast_zmod_val]
  have hnunit : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime _ _).mpr h.symm
  have hmunit : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr h
  have hf : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
    constructor
    · intro p q hpq
      apply Prod.ext
      · apply hnunit.mul_left_cancel
        have hh := congrArg (ZMod.castHom (dvd_mul_right m n) (ZMod m)) hpq
        simpa only [hM] using hh
      · apply hmunit.mul_left_cancel
        have hh := congrArg (ZMod.castHom (dvd_mul_left n m) (ZMod n)) hpq
        simpa only [hN] using hh
    · simp [Fintype.card_prod, ZMod.card]
  symm
  rw [QG, QG, sum_mul_sum]
  rw [← Fintype.sum_prod_type (fun p : ZMod m × ZMod n =>
    ZMod.stdAddChar (((a * n : ℤ) : ZMod m) * p.1 ^ 2) *
      ZMod.stdAddChar (((a * m : ℤ) : ZMod n) * p.2 ^ 2))]
  calc
    (∑ p : ZMod m × ZMod n,
      ZMod.stdAddChar (((a * n : ℤ) : ZMod m) * p.1 ^ 2) *
        ZMod.stdAddChar (((a * m : ℤ) : ZMod n) * p.2 ^ 2)) =
      ∑ p : ZMod m × ZMod n, ZMod.stdAddChar ((a : ZMod (m * n)) * (f p) ^ 2) := by
      apply sum_congr rfl
      intro p _
      simpa [EC, f, mul_assoc] using (EC_CRT_sq m n a (p.1.val : ℤ) (p.2.val : ℤ)).symm
    _ = QG (m * n) a := by
      exact Fintype.sum_bijective f hf _ _ (fun p => rfl)

private lemma EC_two_sum_four (t : ℤ) :
    (∑ y ∈ range 4, EC 2 (t * y)) = if (t : ZMod 2) = 0 then 4 else 0 := by
  have h := char_sum (t : ZMod 2)
  change (∑ x : Fin 2, ZMod.stdAddChar ((t : ZMod 2) * (show ZMod 2 from x))) = _ at h
  simp only [Fin.sum_univ_two] at h
  norm_num [EC, sum_range_succ] at h ⊢
  simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide, mul_zero, mul_one, AddChar.map_zero_eq_one]
  split_ifs at h ⊢ <;> linear_combination 2 * h

private lemma EC_shift_four (n : ℕ) [NeZero n] (hn : 4 ∣ n) (a x y : ℤ) :
    EC (4 * n) (a * (x + n * y) ^ 2) = EC (4 * n) (a * x ^ 2) * EC 2 (a * x * y) := by
  have h : a * (x + n * y) ^ 2 = a * x ^ 2 + (n : ℤ) * (2 * a * x * y + a * n * y ^ 2) := by ring
  rw [h, EC_add, EC_mul_left]
  congr 1
  have hn0 : (n : ZMod 4) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hn
  have h4 : EC 4 (2 * a * x * y + a * n * y ^ 2) = EC 4 (2 * (a * x * y)) := by
    simp [EC, hn0, mul_assoc]
  rw [h4]
  exact EC_mul_right 2 2 _

private lemma EC_half_shift (m : ℕ) [NeZero m] (a x y : ℤ) :
    EC (4 * m) (a * (x + (2 * m : ℕ) * y) ^ 2) = EC (4 * m) (a * x ^ 2) := by
  have h : a * (x + (2 * m : ℕ) * y) ^ 2 = a * x ^ 2 +
      (4 * m : ℕ) * (a * x * y + a * m * y ^ 2) := by push_cast; ring
  rw [h, EC_period]

private lemma QG_half (m : ℕ) [NeZero m] (a : ℤ) :
    QG (4 * m) a = 2 * ∑ x ∈ range (2 * m), EC (4 * m) (a * (x : ℤ) ^ 2) := by
  rw [QG_sum_range]
  conv_lhs => arg 1; rw [show 4 * m = (2 * m) * 2 by omega]
  rw [sum_range_stride]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hh (x y : ℕ) : EC (4 * m) (a * ((x : ℤ) + 2 * m * y) ^ 2) =
      EC (4 * m) (a * (x : ℤ) ^ 2) := by
    simpa using EC_half_shift m a x y
  simp_rw [hh]
  simp [← mul_sum]

lemma QG_four_lift (m : ℕ) [NeZero m] (a : ℤ) (ha : Odd a) :
    QG (4 * (4 * m)) a = 2 * QG (4 * m) a := by
  have ha2 : (a : ZMod 2) = 1 := by
    rw [← ZMod.intCast_mod a 2]
    have := Int.odd_iff.mp ha
    norm_num [this]
  rw [QG_sum_range]
  conv_lhs => arg 1; rw [mul_comm 4 (4 * m)]
  rw [sum_range_stride]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hshift (x y : ℕ) : EC (4 * (4 * m)) (a * ((x : ℤ) + 4 * m * y) ^ 2) =
      EC (4 * (4 * m)) (a * (x : ℤ) ^ 2) * EC 2 (a * x * y) := by
    simpa using EC_shift_four (4 * m) (dvd_mul_right 4 m) a x y
  simp_rw [hshift, ← mul_sum, EC_two_sum_four]
  have hcast (x : ℕ) : ((a * x : ℤ) : ZMod 2) = (x : ZMod 2) := by simp [ha2]
  simp only [hcast]
  have hN : 4 * m = 2 * (2 * m) := by omega
  conv_lhs => arg 1; rw [hN]
  rw [sum_range_blocks]
  simp only [sum_range_succ, sum_range_zero, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_one,
    add_zero]
  have hx0 (x : ℕ) : ((2 * x : ℕ) : ZMod 2) = 0 := by simp [show (2 : ZMod 2) = 0 by decide]
  have hx1 (x : ℕ) : ((2 * x + 1 : ℕ) : ZMod 2) = 1 := by simp [show (2 : ZMod 2) = 0 by decide]
  simp_rw [hx0, hx1]
  norm_num only [zero_ne_one, one_ne_zero, if_true, if_false, mul_zero, add_zero]
  have he (x : ℕ) : EC (4 * (4 * m)) (a * ((2 * x : ℕ) : ℤ) ^ 2) =
      EC (4 * m) (a * (x : ℤ) ^ 2) := by
    have h : a * ((2 * x : ℕ) : ℤ) ^ 2 = (4 : ℤ) * (a * (x : ℤ) ^ 2) := by push_cast; ring
    rw [h]
    exact EC_mul_right 4 (4 * m) _
  simp_rw [he]
  rw [QG_half]
  simp only [zero_add, ← sum_mul]
  ring

private lemma char_pow_val (n : ℕ) [NeZero n] (x : ZMod n) :
    ZMod.stdAddChar x = ZMod.stdAddChar (1 : ZMod n) ^ x.val := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private lemma char_two_one : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
  have h := char_nat (N := 2) 1
  norm_num at h
  rw [h]
  convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring

private lemma char_four_one : ZMod.stdAddChar (1 : ZMod 4) = I := by
  have h := char_nat (N := 4) 1
  norm_num at h
  rw [h]
  convert Complex.exp_pi_div_two_mul_I using 1 <;> congr 1 <;> ring

private lemma char_eight_one : ZMod.stdAddChar (1 : ZMod 8) =
    (Real.sqrt 2 / 2 : ℂ) * (1 + I) := by
  have h := char_nat (N := 8) 1
  norm_num at h
  rw [h]
  have he : (2 * Real.pi * I / 8 : ℂ) = (Real.pi / 4 : ℂ) * I := by ring
  rw [he, Complex.exp_mul_I]
  have hcos : Complex.cos (Real.pi / 4 : ℂ) = (Real.sqrt 2 / 2 : ℂ) := by
    simpa only [Complex.ofReal_cos, Complex.ofReal_div, Complex.ofReal_ofNat] using
      congrArg Complex.ofReal Real.cos_pi_div_four
  have hsin : Complex.sin (Real.pi / 4 : ℂ) = (Real.sqrt 2 / 2 : ℂ) := by
    simpa only [Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_ofNat] using
      congrArg Complex.ofReal Real.sin_pi_div_four
  rw [hcos, hsin]
  ring

private lemma char_four (z : ZMod 4) : ZMod.stdAddChar z = I ^ z.val := by
  rw [char_pow_val, char_four_one]

private lemma char_eight (z : ZMod 8) : ZMod.stdAddChar z =
    ((Real.sqrt 2 / 2 : ℂ) * (1 + I)) ^ z.val := by
  rw [char_pow_val, char_eight_one]

private lemma chi8_sq (a : ℤ) (ha : Odd a) : ZMod.χ₈ a ^ 2 = 1 := by
  have ha2 := Int.odd_iff.mp ha
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  simp only [ha2, one_ne_zero, if_false]
  split_ifs <;> norm_num

private lemma chi4_sq (a : ℤ) (ha : Odd a) : ZMod.χ₄ a ^ 2 = 1 := by
  have ha2 := Int.odd_iff.mp ha
  rw [ZMod.χ₄_int_eq_if_mod_four]
  simp only [ha2, one_ne_zero, if_false]
  split_ifs <;> norm_num

lemma QG_two (a : ℤ) (ha : Odd a) : QG 2 a = 0 := by
  have ha2 : (a : ZMod 2) = 1 := by
    rw [← ZMod.intCast_mod a 2]
    norm_num [Int.odd_iff.mp ha]
  rw [ha2, QG]
  change (∑ x : Fin 2, ZMod.stdAddChar ((1 : ZMod 2) * (show ZMod 2 from x) ^ 2)) = _
  norm_num [Fin.sum_univ_succ, char_two_one]


private lemma QG_four_table (a : ZMod 4) : QG 4 a = 2 * (1 + ZMod.stdAddChar a) := by
  unfold QG
  change (∑ x : Fin 4, ZMod.stdAddChar (a * (show ZMod 4 from x) ^ 2)) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  change ZMod.stdAddChar (a * (0 : ZMod 4) ^ 2) + (ZMod.stdAddChar (a * (1 : ZMod 4) ^ 2) +
    (ZMod.stdAddChar (a * (2 : ZMod 4) ^ 2) + (ZMod.stdAddChar (a * (3 : ZMod 4) ^ 2) + 0))) = _
  rw [show (2 : ZMod 4) ^ 2 = 0 by decide, show (3 : ZMod 4) ^ 2 = 1 by decide]
  simp only [zero_pow two_ne_zero, one_pow, mul_zero, mul_one, AddChar.map_zero_eq_one]
  ring

private lemma QG_eight_table (a : ZMod 8) :
    QG 8 a = 2 + 4 * ZMod.stdAddChar a + 2 * ZMod.stdAddChar (a * 4) := by
  unfold QG
  change (∑ x : Fin 8, ZMod.stdAddChar (a * (show ZMod 8 from x) ^ 2)) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  change ZMod.stdAddChar (a * (0 : ZMod 8) ^ 2) + (ZMod.stdAddChar (a * (1 : ZMod 8) ^ 2) +
    (ZMod.stdAddChar (a * (2 : ZMod 8) ^ 2) + (ZMod.stdAddChar (a * (3 : ZMod 8) ^ 2) +
    (ZMod.stdAddChar (a * (4 : ZMod 8) ^ 2) + (ZMod.stdAddChar (a * (5 : ZMod 8) ^ 2) +
    (ZMod.stdAddChar (a * (6 : ZMod 8) ^ 2) + (ZMod.stdAddChar (a * (7 : ZMod 8) ^ 2) + 0))))))) = _
  rw [show (2 : ZMod 8) ^ 2 = 4 by decide, show (3 : ZMod 8) ^ 2 = 1 by decide,
    show (4 : ZMod 8) ^ 2 = 0 by decide, show (5 : ZMod 8) ^ 2 = 1 by decide,
    show (6 : ZMod 8) ^ 2 = 4 by decide, show (7 : ZMod 8) ^ 2 = 1 by decide]
  simp only [zero_pow two_ne_zero, one_pow, mul_zero, mul_one, AddChar.map_zero_eq_one]
  ring

private lemma QG_four (a : ℤ) (ha : Odd a) :
    QG 4 a = 2 * (1 + I * (ZMod.χ₄ a : ℂ)) := by
  have ha2 := Int.odd_iff.mp ha
  have hb : 0 ≤ a % 4 := Int.emod_nonneg _ (by decide : (4 : ℤ) ≠ 0)
  have hc : a % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  have he : (a : ZMod 4) = ((a % 4 : ℤ) : ZMod 4) := (ZMod.intCast_mod a 4).symm
  rw [QG_four_table, ZMod.χ₄_int_eq_if_mod_four]
  conv_lhs => rw [he]
  interval_cases hmod : a % 4 <;> try omega
  all_goals norm_num [char_four, ha2, ZMod.val, Fin.coe_ofNat_eq_mod]

private lemma sqrt_two_pow (k : ℕ) : (Real.sqrt 2 : ℂ) ^ k =
    (2 : ℂ) ^ (k / 2) * (Real.sqrt 2 : ℂ) ^ (k % 2) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  conv_lhs => rw [← Nat.div_add_mod k 2]
  rw [pow_add, pow_mul, hs]

private lemma QG_eight (a : ℤ) (ha : Odd a) :
    QG 8 a = (2 * Real.sqrt 2 : ℂ) * (ZMod.χ₈ a : ℂ) * (1 + I * (ZMod.χ₄ a : ℂ)) := by
  have ha2 := Int.odd_iff.mp ha
  have hb : 0 ≤ a % 8 := Int.emod_nonneg _ (by decide : (8 : ℤ) ≠ 0)
  have hc : a % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  have he : (a : ZMod 8) = ((a % 8 : ℤ) : ZMod 8) := (ZMod.intCast_mod a 8).symm
  have h4 : a % 4 = a % 8 % 4 := (Int.emod_emod_of_dvd a (by decide : (4 : ℤ) ∣ 8)).symm
  rw [QG_eight_table, ZMod.χ₈_int_eq_if_mod_eight, ZMod.χ₄_int_eq_if_mod_four]
  conv_lhs => rw [he]
  rw [h4]
  interval_cases hmod : a % 8 <;> try omega
  all_goals
    norm_num [char_eight, ha2, ZMod.val, Fin.coe_ofNat_eq_mod]
    ring_nf
    norm_num [sqrt_two_pow 3, sqrt_two_pow 4, sqrt_two_pow 5, sqrt_two_pow 6, sqrt_two_pow 7,
      I_pow_eq_pow_mod]
    ring_nf
    norm_num [I_sq, I_pow_three]
    <;> ring

lemma QG_congr_level {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (a : ℤ) :
    QG m a = QG n a := by subst n; rfl

lemma QG_pow_two (k : ℕ) (a : ℤ) (ha : Odd a) :
    QG (2 ^ (k + 2)) a = (Real.sqrt (2 ^ (k + 2) : ℕ) : ℂ) *
      (ZMod.χ₈ a : ℂ) ^ (k + 2) * (1 + I * (ZMod.χ₄ a : ℂ)) := by
  have hc : (ZMod.χ₈ a : ℂ) ^ 2 = 1 := by exact_mod_cast chi8_sq a ha
  induction k using Nat.twoStepInduction with
  | zero =>
    change QG 4 a = (Real.sqrt 4 : ℂ) * (ZMod.χ₈ a : ℂ) ^ 2 * (1 + I * (ZMod.χ₄ a : ℂ))
    rw [hc, mul_one, show Real.sqrt (4 : ℝ) = 2 by norm_num]
    exact QG_four a ha
  | one =>
    have hs : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    change QG 8 a = (Real.sqrt 8 : ℂ) * (ZMod.χ₈ a : ℂ) ^ 3 * (1 + I * (ZMod.χ₄ a : ℂ))
    rw [show 3 = 2 + 1 by rfl, pow_add (ZMod.χ₈ a : ℂ), hc, pow_one, one_mul, hs, Complex.ofReal_mul]
    exact QG_eight a ha
  | more k ih ih' =>
    have hn1 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    have hn2 : 2 ^ (k + 2 + 2) = 4 * (4 * 2 ^ k) := by rw [pow_add, hn1]; ring
    have hr : QG (2 ^ (k + 2 + 2)) a = 2 * QG (2 ^ (k + 2)) a := by
      rw [QG_congr_level hn2, QG_congr_level hn1]
      exact QG_four_lift (2 ^ k) a ha
    have hs : Real.sqrt (2 ^ (k + 2 + 2) : ℕ) = 2 * Real.sqrt (2 ^ (k + 2) : ℕ) := by
      rw [pow_add, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
      norm_num
      ring
    rw [hr, ih, hs, Complex.ofReal_mul, Complex.ofReal_ofNat, pow_add (ZMod.χ₈ a : ℂ) (k + 2) 2, hc, mul_one]
    ring

lemma QG_odd_coeff (n : ℕ) [NeZero n] (hn : Odd n) (a : ZMod n) (ha : IsUnit a) :
    QG n a = (signChar n a : ℂ) * (if n % 4 = 1 then 1 else I) * (Real.sqrt n : ℂ) := by
  rw [← ha.unit_spec, QG_unit_odd hn, QG_one_odd hn]
  rw [ha.unit_spec]
  ring

lemma QG_even_im (k t : ℕ) [NeZero t] (ht : Odd t) (a : ℕ)
    (ha : a.Coprime (2 ^ (k + 2) * t)) :
    (QG (2 ^ (k + 2) * t) (a : ZMod (2 ^ (k + 2) * t))).im =
      Real.sqrt (2 ^ (k + 2) * t : ℕ) * (signChar t (a : ZMod t) : ℝ) *
        (ZMod.χ₈ a : ℝ) ^ (k + 2) * (if t % 4 = 1 then (ZMod.χ₄ a : ℝ) else 1) := by
  have hat := (Nat.coprime_mul_iff_right.mp ha).2
  have ha2 : a.Coprime 2 := Nat.Coprime.of_dvd_right
    (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : k + 2 ≠ 0)) t) ha
  have hao : Odd a := Nat.coprime_two_right.mp ha2
  have hai : Odd (a : ℤ) := by exact_mod_cast hao
  have hti : Odd (t : ℤ) := by exact_mod_cast ht
  have hcop : (2 ^ (k + 2)).Coprime t := (Nat.coprime_two_left.mpr ht).pow_left _
  have hau : IsUnit (a : ZMod t) := (ZMod.isUnit_iff_coprime _ _).mpr hat
  have hap : IsUnit (((a : ℤ) * (2 ^ (k + 2) : ℕ) : ℤ) : ZMod t) := by
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using
      hau.mul ((unit_two_of_odd ht).pow (k + 2))
  have hχt : (ZMod.χ₈ t : ℂ) ^ 2 = 1 := by
    exact_mod_cast chi8_sq (t : ℤ) hti
  have hroot : (Real.sqrt (2 ^ (k + 2) * t : ℕ) : ℂ) =
      (Real.sqrt (2 ^ (k + 2) : ℕ) : ℂ) * (Real.sqrt t : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  have hq : QG (2 ^ (k + 2) * t) (a : ZMod (2 ^ (k + 2) * t)) =
      (Real.sqrt (2 ^ (k + 2) * t : ℕ) : ℂ) * (signChar t (a : ZMod t) : ℂ) *
        (ZMod.χ₈ a : ℂ) ^ (k + 2) *
        ((if t % 4 = 1 then 1 else I) * (1 + I * ((ZMod.χ₄ a : ℂ) * (ZMod.χ₄ t : ℂ)))) := by
    rw [show (a : ZMod (2 ^ (k + 2) * t)) = ((a : ℤ) : ZMod (2 ^ (k + 2) * t)) by simp,
      QG_CRT (2 ^ (k + 2)) t hcop,
      QG_pow_two k ((a : ℤ) * t) (hai.mul hti),
      QG_odd_coeff t ht _ hap]
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, map_mul, map_pow,
      signChar_two ht, Int.cast_pow, mul_pow]
    rw [hroot]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, signChar_two ht]
    have hpow : (ZMod.χ₈ t : ℂ) ^ (k + 2) * (ZMod.χ₈ t : ℂ) ^ (k + 2) = 1 := by
      rw [← mul_pow, ← pow_two, hχt, one_pow]
    calc
      _ = (Real.sqrt (2 ^ (k + 2) : ℕ) : ℂ) * (Real.sqrt t : ℂ) *
        (signChar t (a : ZMod t) : ℂ) * (ZMod.χ₈ a : ℂ) ^ (k + 2) *
        ((if t % 4 = 1 then 1 else I) * (1 + I * ((ZMod.χ₄ a : ℂ) * (ZMod.χ₄ t : ℂ)))) *
        ((ZMod.χ₈ t : ℂ) ^ (k + 2) * (ZMod.χ₈ t : ℂ) ^ (k + 2)) := by
          push_cast
          ring
      _ = _ := by rw [hpow, mul_one]; push_cast; rfl
  have hχ4t : ZMod.χ₄ t = if t % 4 = 1 then 1 else -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four, Nat.odd_iff.mp ht]
    norm_num
  rw [hq]
  split_ifs with h4
  · simp only [hχ4t, h4, if_true, Int.cast_one, mul_one, one_mul]
    simp only [← Int.cast_pow, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, zero_mul, mul_zero, add_zero, zero_add, mul_one, one_mul, sub_zero]
  · simp only [hχ4t, h4, if_false, Int.cast_neg, Int.cast_one, mul_neg_one]
    simp only [← Int.cast_pow, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
      zero_mul, mul_zero, add_zero, zero_add, mul_one, one_mul, neg_zero, sub_zero]

def natChar (n : ℕ) (χ : MulChar (ZMod n) ℤ) : ℕ →* ℤ :=
  χ.toMonoidHom.comp (Nat.castRingHom (ZMod n)).toMonoidHom

@[simp] lemma natChar_apply (n : ℕ) (χ : MulChar (ZMod n) ℤ) (a : ℕ) :
    natChar n χ a = χ a := rfl

lemma quad_abs {x : ℤ} (h : x = 0 ∨ x = 1 ∨ x = -1) : |(x : ℝ)| ≤ 1 := by
  rcases h with h | h | h <;> simp [h]

lemma chi8_bound (a : ℕ) : |(ZMod.χ₈ a : ℝ)| ≤ 1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  split_ifs <;> norm_num

lemma chi4_bound (a : ℕ) : |(ZMod.χ₄ a : ℝ)| ≤ 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

lemma QG_nat_congr_level {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (a : ℕ) :
    QG m (a : ZMod m) = QG n (a : ZMod n) := by subst n; rfl

lemma QG_unit_im_character (n : ℕ) [NeZero n] :
    ∃ (χ : ℕ →* ℤ) (c : ℝ), 0 ≤ c ∧ (∀ a, |(χ a : ℝ)| ≤ 1) ∧
      ∀ a : ℕ, (if a.Coprime n then (QG n a).im else 0) = c * (χ a : ℝ) := by
  obtain ⟨j, t, ht, he⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne n)
  have ht0 : t ≠ 0 := by intro h; subst t; simp at ht
  letI : NeZero t := ⟨ht0⟩
  subst n
  rcases j with _ | _ | k
  · simp_rw [QG_nat_congr_level (show 2 ^ 0 * t = t by simp)]
    simp only [pow_zero, one_mul]
    by_cases h4 : t % 4 = 1
    · refine ⟨1, 0, le_rfl, fun _ => by norm_num, fun a => ?_⟩
      split_ifs with ha
      · rw [QG_odd_coeff t ht _ ((ZMod.isUnit_iff_coprime _ _).mpr ha)]
        simp [h4]
      · simp
    · refine ⟨natChar t (signChar t), Real.sqrt t, Real.sqrt_nonneg _,
        fun a => quad_abs (signChar_quad (a : ZMod t)), fun a => ?_⟩
      simp only [natChar_apply]
      split_ifs with ha
      · rw [QG_odd_coeff t ht _ ((ZMod.isUnit_iff_coprime _ _).mpr ha)]
        simp [h4, mul_comm]
      · rw [(signChar t).map_nonunit (by rwa [ZMod.isUnit_iff_coprime])]
        simp
  · refine ⟨1, 0, le_rfl, fun _ => by norm_num, fun a => ?_⟩
    split_ifs with ha
    · have hao : Odd a := Nat.coprime_two_right.mp (Nat.coprime_mul_iff_right.mp ha).1
      have hat : Odd ((a : ℤ) * t) := by exact_mod_cast hao.mul ht
      have heq : QG (2 ^ (0 + 1) * t) (a : ZMod (2 ^ (0 + 1) * t)) = 0 := by
        rw [QG_nat_congr_level (show 2 ^ (0 + 1) * t = 2 * t by simp)]
        rw [show (a : ZMod (2 * t)) = ((a : ℤ) : ZMod (2 * t)) by simp]
        rw [QG_CRT 2 t (Nat.coprime_two_left.mpr ht), QG_two _ hat, zero_mul]
      rw [heq]; simp
    · simp
  · let χ : ℕ →* ℤ := natChar t (signChar t) * natChar 8 ZMod.χ₈ ^ (k + 2) *
        (if t % 4 = 1 then natChar 4 ZMod.χ₄ else 1)
    have hχ (a : ℕ) : χ a = signChar t (a : ZMod t) * ZMod.χ₈ a ^ (k + 2) *
        (if t % 4 = 1 then ZMod.χ₄ a else 1) := by
      simp only [χ, MonoidHom.mul_apply, MonoidHom.pow_apply, natChar_apply]
      split_ifs <;> rfl
    refine ⟨χ, Real.sqrt (2 ^ (k + 2) * t : ℕ), Real.sqrt_nonneg _, ?_, ?_⟩
    · intro a
      rw [hχ]
      push_cast
      rw [abs_mul, abs_mul, abs_pow]
      have h1 := quad_abs (signChar_quad (a : ZMod t))
      have h2 : |(ZMod.χ₈ a : ℝ)| ^ (k + 2) ≤ 1 := pow_le_one₀ (abs_nonneg _) (chi8_bound a)
      have h3 : |(if t % 4 = 1 then (ZMod.χ₄ a : ℝ) else 1)| ≤ 1 := by
        split_ifs; exact chi4_bound a; norm_num
      calc
        _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
        _ = 1 := by norm_num
    · intro a
      rw [hχ]
      by_cases ha : a.Coprime (2 ^ (k + 2) * t)
      · rw [if_pos ha, QG_even_im k t ht a ha]
        push_cast
        ring
      · rw [if_neg ha]
        have hz : signChar t (a : ZMod t) * ZMod.χ₈ a ^ (k + 2) = 0 := by
          by_cases hat : a.Coprime t
          · have ha2 : ¬ Odd a := by
              intro hao
              exact ha (Nat.coprime_mul_iff_right.mpr
                ⟨(Nat.coprime_two_right.mpr hao).pow_right _, hat⟩)
            have heven : a % 2 = 0 := by rw [Nat.odd_iff] at ha2; omega
            have hz8 : ZMod.χ₈ a = 0 := by simp only [ZMod.χ₈_nat_eq_if_mod_eight, heven, ite_true]
            rw [hz8, zero_pow (by omega), mul_zero]
          · rw [(signChar t).map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
        rw [hz, zero_mul, Int.cast_zero, mul_zero]


open Filter Topology

set_option maxHeartbeats 800000 in
lemma character_series_nonneg (χ : ℕ →* ℤ) (hχ : ∀ a, |(χ a : ℝ)| ≤ 1)
    {s : ℝ} (hs : 1 < s) : 0 ≤ ∑' a : ℕ, (χ a : ℝ) * (a : ℝ) ^ (-s) := by
  let f : ℕ →*₀ ℝ :=
    { toFun := fun a => (χ a : ℝ) * (a : ℝ) ^ (-s)
      map_zero' := by simp [Real.zero_rpow (by linarith : -s ≠ 0)]
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul, Int.cast_mul, Nat.cast_mul,
          Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
        ring }
  have hsum : Summable (‖f ·‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -s < -1))
    change |(χ a : ℝ) * (a : ℝ) ^ (-s)| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    simpa using mul_le_mul_of_nonneg_right (hχ a) (Real.rpow_nonneg (Nat.cast_nonneg a) (-s))
  have hlim := EulerProduct.eulerProduct_completely_multiplicative (f := f) hsum
  refine ge_of_tendsto hlim (Eventually.of_forall fun m => Finset.prod_nonneg fun p hp => ?_)
  have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
  apply inv_nonneg.mpr
  have hnorm := Summable.norm_lt_one (f := f.toMonoidHom) hsum.of_norm hp'.one_lt
  exact sub_nonneg.mpr (le_trans (le_abs_self _) (le_of_lt hnorm))

lemma QG_bound (n : ℕ) [NeZero n] (a : ZMod n) : ‖QG n a‖ ≤ n := by
  calc
    ‖QG n a‖ ≤ ∑ x : ZMod n, ‖ZMod.stdAddChar (a * x ^ 2)‖ := norm_sum_le _ _
    _ = n := by simp [char_norm]

lemma QG_im_series_summable (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : ℕ => (QG n a).im * (a : ℝ) ^ (-s)) := by
  refine Summable.of_norm_bounded ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).mul_left (n : ℝ))
    (fun a => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm _).trans (QG_bound n a))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma QG_unit_series_nonneg (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    0 ≤ ∑' a : ℕ, (if a.Coprime n then (QG n a).im else 0) * (a : ℝ) ^ (-s) := by
  obtain ⟨χ, c, hc, hχ, he⟩ := QG_unit_im_character n
  simp_rw [he, mul_assoc]
  rw [tsum_mul_left]
  exact mul_nonneg hc (character_series_nonneg χ hχ hs)


lemma QG_im_series_nonneg (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    0 ≤ ∑' a : ℕ, (QG n a).im * (a : ℝ) ^ (-s) := by
  classical
  let F (d a : ℕ) : ℝ := if a.gcd n = d then (QG n a).im * (a : ℝ) ^ (-s) else 0
  have he (a : ℕ) : (QG n a).im * (a : ℝ) ^ (-s) = ∑ d ∈ n.divisors, F d a := by
    simp only [F]
    simp [Finset.sum_ite_eq, Nat.mem_divisors, NeZero.ne n, Nat.gcd_dvd_right]
  have hsum (d : ℕ) : Summable (F d) := by
    apply Summable.of_norm_bounded (QG_im_series_summable n hs).norm
    intro a
    dsimp only [F]
    split_ifs <;> simp <;> positivity
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun d _ => hsum d)]
  apply Finset.sum_nonneg
  intro d hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := by intro h; subst d; exact NeZero.ne n (by simpa using hdvd)
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hq0 : n / d ≠ 0 := by intro h; rw [h, mul_zero] at heq; exact NeZero.ne n heq.symm
  letI : NeZero d := ⟨hd0⟩
  letI : NeZero (n / d) := ⟨hq0⟩
  have hi : Function.Injective (fun a : ℕ => d * a) := fun _ _ h => mul_left_cancel₀ hd0 h
  have hrange : Function.support (F d) ⊆ Set.range (fun a : ℕ => d * a) := by
    intro a ha
    have hag : a.gcd n = d := by
      by_contra h
      exact ha (if_neg h)
    exact ⟨a / d, Nat.mul_div_cancel' (hag ▸ Nat.gcd_dvd_left a n)⟩
  rw [← hi.tsum_eq hrange]
  have hterm (a : ℕ) : F d (d * a) = ((d : ℝ) * (d : ℝ) ^ (-s)) *
      ((if a.Coprime (n / d) then (QG (n / d) a).im else 0) * (a : ℝ) ^ (-s)) := by
    have hg : (d * a).gcd n = d ↔ a.Coprime (n / d) := by
      conv_lhs => rw [← heq, Nat.gcd_mul_left]
      change d * a.gcd (n / d) = d ↔ a.gcd (n / d) = 1
      simpa only [mul_one] using (mul_right_inj' hd0 : d * a.gcd (n / d) = d * 1 ↔ a.gcd (n / d) = 1)
    have hQ : QG n ((d * a : ℕ) : ZMod n) = (d : ℂ) * QG (n / d) (a : ZMod (n / d)) := by
      rw [QG_nat_congr_level heq.symm]
      convert QG_level_mul d (n / d) (a : ℤ) using 1 <;> simp
    dsimp only [F]
    simp only [hg]
    split_ifs with ha
    · rw [hQ]
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
        Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg a)]
      ring
    · ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
    (QG_unit_series_nonneg (n / d) hs)

end QuadraticBias

noncomputable section
open Finset Filter Complex
open scoped Topology
namespace QuadraticBias

lemma rpow_step_bound (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2) :
    |((n : ℝ) + 1) ^ (-s) - ((n : ℝ) + 2) ^ (-s)| ≤
      2 * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  have hn : 1 ≤ (n : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun x : ℝ => x ^ (-s))
    (f' := fun x : ℝ => -s * x ^ (-s - 1))
    (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (C := 2 * ((n : ℝ) + 1) ^ (-2 : ℝ))
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))).hasDerivWithinAt)
    (fun x hx => ?_) ((n : ℝ) + 2) (by constructor <;> linarith)
  · simpa only [Real.norm_eq_abs, show (n : ℝ) + 2 - ((n : ℝ) + 1) = 1 by ring, mul_one,
      abs_sub_comm] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by linarith [hs.1] : 0 ≤ s),
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : 0 ≤ x) _)]
    apply mul_le_mul hs.2 _ (Real.rpow_nonneg (by linarith [hx.1]) _) (by norm_num)
    exact (Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith [hs.1])).trans
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith [hs.1]))

def prefixSum (f : ℕ → ℂ) (n : ℕ) : ℂ := ∑ i ∈ range n, f i

def boundary (f : ℕ → ℂ) (s : ℝ) : ℂ :=
  ∑' n : ℕ, (((n : ℝ) + 1) ^ (-s) - ((n : ℝ) + 2) ^ (-s)) • prefixSum f (n + 1)

lemma boundary_continuous (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖prefixSum f n‖ ≤ C) : ContinuousOn (boundary f) (Set.Icc 1 2) := by
  have hsum : Summable (fun n : ℕ => (2 * C) * ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  refine continuousOn_tsum (u := fun n : ℕ => (2 * C) * ((n : ℝ) + 1) ^ (-2 : ℝ)) ?_ hsum ?_
  · intro n
    apply Continuous.continuousOn
    exact (((Real.continuous_const_rpow (by positivity : (n : ℝ) + 1 ≠ 0)).comp continuous_neg).sub
      ((Real.continuous_const_rpow (by positivity : (n : ℝ) + 2 ≠ 0)).comp continuous_neg)).smul continuous_const
  · intro n s hs
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (2 * ((n : ℝ) + 1) ^ (-2 : ℝ)) * C :=
        mul_le_mul (rpow_step_bound n hs) (hf _) (norm_nonneg _) (by positivity)
      _ = _ := by ring

lemma boundary_summable (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖prefixSum f n‖ ≤ C) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2) :
    Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (-s) - ((n : ℝ) + 2) ^ (-s)) • prefixSum f (n + 1)) := by
  have hsum : Summable (fun n : ℕ => (2 * C) * ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  apply Summable.of_norm_bounded hsum
  intro n
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (2 * ((n : ℝ) + 1) ^ (-2 : ℝ)) * C :=
      mul_le_mul (rpow_step_bound n hs) (hf _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma boundary_partial_tendsto (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖prefixSum f n‖ ≤ C) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2) :
    Tendsto (fun m : ℕ => ∑ n ∈ range m, ((n : ℝ) + 1) ^ (-s) • f n) atTop (𝓝 (boundary f s)) := by
  have hzero : Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ (-s) • prefixSum f (m + 1)) atTop (𝓝 0) := by
    apply NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      (ε := fun m : ℕ => ((m : ℝ) + 1) ^ (-s)) (f := fun m => prefixSum f (m + 1))
    · exact (tendsto_rpow_neg_atTop (by linarith [hs.1] : 0 < s)).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    · exact ⟨C, eventually_map.mpr (Eventually.of_forall fun m : ℕ => hf (m + 1))⟩
  have hsum := (boundary_summable f hC hf hs).hasSum.tendsto_sum_nat
  have hlim := hzero.add hsum
  have he (m : ℕ) : (∑ n ∈ range (m + 1), ((n : ℝ) + 1) ^ (-s) • f n) =
      ((m : ℝ) + 1) ^ (-s) • prefixSum f (m + 1) +
      ∑ n ∈ range m, (((n : ℝ) + 1) ^ (-s) - ((n : ℝ) + 2) ^ (-s)) • prefixSum f (n + 1) := by
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    simp only [prefixSum, sub_smul, sum_sub_distrib]
    abel
  have hlim' : Tendsto (fun m : ℕ => ∑ n ∈ range (m + 1), ((n : ℝ) + 1) ^ (-s) • f n) atTop (𝓝 (boundary f s)) := by
    simpa only [he, zero_add, boundary] using hlim
  exact (tendsto_add_atTop_iff_nat 1).mp hlim'


lemma geom_prefix_bound (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (m : ℕ) :
    ‖prefixSum (fun n => z ^ (n + 1)) m‖ ≤ 2 / ‖z - 1‖ := by
  rw [prefixSum]
  simp_rw [pow_succ]
  rw [← sum_mul, geom_sum_eq hz1, norm_mul, hz, mul_one, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ m - 1‖ ≤ ‖z ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz]; norm_num

lemma unit_one_sub_slitPlane {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := by
  have hre : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
  have hlt : z.re < 1 := by
    by_contra h
    have he : z.re = 1 := le_antisymm hre (not_lt.mp h)
    have him : z.im = 0 := by
      have hn := Complex.sq_norm z
      rw [hz, Complex.normSq_apply, he] at hn
      nlinarith [sq_nonneg z.im]
    exact hz1 (Complex.ext he him)
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))

lemma geom_boundary_one (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    boundary (fun n => z ^ (n + 1)) 1 = -Complex.log (1 - z) := by
  let C := 2 / ‖z - 1‖
  have hC : 0 ≤ C := by positivity
  have hb := boundary_partial_tendsto (fun n => z ^ (n + 1)) hC (geom_prefix_bound z hz hz1)
    (s := 1) (by norm_num)
  have hpart : Tendsto (fun m => ∑ n ∈ range m, z ^ n / (n : ℂ)) atTop
      (𝓝 (boundary (fun n => z ^ (n + 1)) 1)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have he (m : ℕ) : (∑ n ∈ range (m + 1), z ^ n / (n : ℂ)) =
        ∑ n ∈ range m, ((n : ℝ) + 1) ^ (-(1 : ℝ)) • z ^ (n + 1) := by
      rw [sum_range_succ']
      simp only [pow_zero, Nat.cast_zero, div_zero, add_zero]
      apply sum_congr rfl
      intro n hn
      rw [Real.rpow_neg_one]
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_add,
        Complex.ofReal_natCast, Complex.ofReal_one, Nat.cast_add, Nat.cast_one]
      ring
    simpa only [he] using hb
  have ha := (tendsto_map'_iff.mp (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hpart))
  have hlog : Tendsto (fun r : ℝ => -Complex.log (1 - z * (r : ℂ))) (𝓝[<] 1)
      (𝓝 (-Complex.log (1 - z))) := by
    have hi : Tendsto (fun r : ℝ => 1 - z * (r : ℂ)) (𝓝 1) (𝓝 (1 - z)) := by
      simpa only [Complex.ofReal_one, mul_one] using
        (show ContinuousAt (fun r : ℝ => 1 - z * (r : ℂ)) 1 by fun_prop).tendsto
    exact ((continuousAt_clog (unit_one_sub_slitPlane hz hz1)).tendsto.comp hi).neg.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique ha
  apply hlog.congr'
  have hrpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hrpos, self_mem_nhdsWithin] with r hr0 hr1
  have hnorm : ‖z * (r : ℂ)‖ < 1 := by
    rw [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  rw [← (Complex.hasSum_taylorSeries_neg_log hnorm).tsum_eq]
  apply tsum_congr
  intro n
  simp only [mul_pow]
  ring

lemma geom_boundary_series (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    {s : ℝ} (hs : s ∈ Set.Ioc (1 : ℝ) 2) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) • z ^ n = boundary (fun n => z ^ (n + 1)) s := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s) • z ^ n) := by
    refine Summable.of_norm_bounded (Real.summable_nat_rpow.mpr (by linarith [hs.1] : -s < -1)) ?_
    intro n
    simp only [norm_smul, norm_pow, hz, one_pow, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), le_refl]
  have he (m : ℕ) : (∑ n ∈ range (m + 1), (n : ℝ) ^ (-s) • z ^ n) =
      ∑ n ∈ range m, ((n : ℝ) + 1) ^ (-s) • z ^ (n + 1) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, Real.zero_rpow (by linarith [hs.1] : -s ≠ 0), zero_smul,
      add_zero, Nat.cast_add, Nat.cast_one]
  have ht := (hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr' (Eventually.of_forall he)
  exact tendsto_nhds_unique ht (boundary_partial_tendsto _ (by positivity : 0 ≤ 2 / ‖z - 1‖)
    (geom_prefix_bound z hz hz1) ⟨hs.1.le, hs.2⟩)


lemma log_one_sub_exp_im {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (-Complex.log (1 - Complex.exp ((2 * θ : ℝ) * I))).im = Real.pi / 2 - θ := by
  have he : 1 - Complex.exp ((2 * θ : ℝ) * I) =
      (2 * Real.sin θ : ℝ) * Complex.exp (((θ - Real.pi / 2 : ℝ) : ℂ) * I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_two_mul, Real.sin_two_mul,
      Real.cos_sub, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    linear_combination -2 * (Complex.sin_sq_add_cos_sq (θ : ℂ))
  rw [he, Complex.neg_im, Complex.log_im, Complex.arg_real_mul _
    (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)), Complex.arg_exp_mul_I]
  rw [(toIocMod_eq_self Real.two_pi_pos).mpr (show θ - Real.pi / 2 ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) by
    constructor <;> linarith [Real.pi_pos])]
  ring

def boundaryExponent (m : ℕ) : ℝ := 1 + 1 / ((m : ℝ) + 1)

lemma boundaryExponent_mem (m : ℕ) : boundaryExponent m ∈ Set.Ioc (1 : ℝ) 2 := by
  have hn : 1 ≤ (m : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  constructor
  · dsimp [boundaryExponent]; exact lt_add_of_pos_right 1 (by positivity)
  · dsimp [boundaryExponent]
    have : 1 / ((m : ℝ) + 1) ≤ 1 := (div_le_one (by positivity : 0 < (m : ℝ) + 1)).mpr hn
    linarith

lemma boundaryExponent_tendsto : Tendsto boundaryExponent atTop (𝓝 1) := by
  simpa only [add_zero] using
    (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

lemma geom_series_tendsto (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun m : ℕ => ∑' n : ℕ, (n : ℝ) ^ (-boundaryExponent m) • z ^ n)
      atTop (𝓝 (-Complex.log (1 - z))) := by
  simp_rw [geom_boundary_series z hz hz1 (boundaryExponent_mem _)]
  rw [← geom_boundary_one z hz hz1]
  have hc := boundary_continuous (fun n => z ^ (n + 1)) (by positivity : 0 ≤ 2 / ‖z - 1‖)
    (geom_prefix_bound z hz hz1) 1 (by norm_num)
  apply hc.tendsto.comp
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ boundaryExponent_tendsto
  exact Eventually.of_forall fun m => ⟨(boundaryExponent_mem m).1.le, (boundaryExponent_mem m).2⟩

end QuadraticBias

namespace QuadraticBias

private lemma char_unit_ne_one (n : ℕ) [NeZero n] {x : ZMod n} (hx : x ≠ 0) :
    ZMod.stdAddChar x ≠ 1 := by
  intro h
  apply hx
  apply ZMod.injective_toCircle
  apply Subtype.ext
  simpa only [AddChar.map_zero_eq_one, Circle.coe_one, ← ZMod.stdAddChar_apply] using h

def residueBias (n : ℕ) (x : ZMod n) : ℝ := if x = 0 then 0 else 1 / 2 - (x.val : ℝ) / n

lemma char_series_tendsto (n : ℕ) [NeZero n] (x : ZMod n) :
    Tendsto (fun m : ℕ => ∑' a : ℕ,
      (ZMod.stdAddChar ((a : ZMod n) * x)).im * (a : ℝ) ^ (-boundaryExponent m))
      atTop (𝓝 (Real.pi * residueBias n x)) := by
  by_cases hx : x = 0
  · subst x
    simpa [residueBias] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hz : ‖ZMod.stdAddChar x‖ = 1 := Circle.norm_coe _
  have hz1 := char_unit_ne_one n hx
  have he (a : ℕ) : ZMod.stdAddChar ((a : ZMod n) * x) = (ZMod.stdAddChar x) ^ a := by
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  have ht := Complex.continuous_im.tendsto _ |>.comp (geom_series_tendsto _ hz hz1)
  have him : (-Complex.log (1 - ZMod.stdAddChar x)).im = Real.pi * residueBias n x := by
    have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
    have hx0 : 0 < (x.val : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx)
    have hxn : (x.val : ℝ) < n := by exact_mod_cast x.val_lt
    have heq : ZMod.stdAddChar x = Complex.exp (((2 * (Real.pi * x.val / n) : ℝ) : ℂ) * I) := by
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
      congr 1
      push_cast
      ring
    rw [heq, log_one_sub_exp_im (div_pos (mul_pos Real.pi_pos hx0) hn)
      ((div_lt_iff₀ hn).mpr (by nlinarith [Real.pi_pos]))]
    simp only [residueBias, hx, if_false]
    ring
  rw [him] at ht
  convert ht using 1
  funext m
  have hsum : Summable (fun a : ℕ => (a : ℝ) ^ (-boundaryExponent m) • (ZMod.stdAddChar x) ^ a) := by
    apply Summable.of_norm_bounded
      (Real.summable_nat_rpow.mpr (by linarith [(boundaryExponent_mem m).1] : -boundaryExponent m < -1))
    intro a
    simp only [norm_smul, norm_pow, hz, one_pow, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg a) _), le_refl]
  dsimp only [Function.comp_apply]
  rw [← (Complex.hasSum_im hsum.hasSum).tsum_eq]
  apply tsum_congr
  intro a
  rw [he]
  simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

lemma sum_residueBias_nonneg (n : ℕ) [NeZero n] : 0 ≤ ∑ x : ZMod n, residueBias n (x ^ 2) := by
  have ht := tendsto_finset_sum (univ : Finset (ZMod n)) (fun x _ => char_series_tendsto n (x ^ 2))
  have he (m : ℕ) : (∑ x : ZMod n, ∑' a : ℕ,
      (ZMod.stdAddChar ((a : ZMod n) * x ^ 2)).im * (a : ℝ) ^ (-boundaryExponent m)) =
      ∑' a : ℕ, (QG n a).im * (a : ℝ) ^ (-boundaryExponent m) := by
    rw [← Summable.tsum_finsetSum]
    · apply tsum_congr
      intro a
      simp only [QG, Complex.im_sum, sum_mul]
    · intro x hx
      apply Summable.of_norm_bounded
        (Real.summable_nat_rpow.mpr (by linarith [(boundaryExponent_mem m).1] : -boundaryExponent m < -1))
      intro a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg a) _)]
      have hnorm : |(ZMod.stdAddChar ((a : ZMod n) * x ^ 2)).im| ≤ 1 :=
        (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe _)
      simpa using mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (Nat.cast_nonneg a) (-boundaryExponent m))
  have hnn : 0 ≤ ∑ x : ZMod n, Real.pi * residueBias n (x ^ 2) :=
    ge_of_tendsto ht (Eventually.of_forall fun m => he m ▸ QG_im_series_nonneg n (boundaryExponent_mem m).1)
  rw [← mul_sum] at hnn
  exact (mul_nonneg_iff_of_pos_left Real.pi_pos).mp hnn


lemma square_residue_sum_bound (n : ℕ) [NeZero n] :
    2 * (∑ x : ZMod n, (x ^ 2).val) ≤ n * (n - 1) := by
  classical
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hn1 : 1 ≤ n := NeZero.pos n
  have he (x : ZMod n) : residueBias n x = (if x = 0 then 0 else (1 / 2 : ℝ)) - (x.val : ℝ) / n := by
    by_cases hx : x = 0
    · subst x; simp [residueBias]
    · simp only [residueBias, hx, if_false]
  have hB := sum_residueBias_nonneg n
  simp_rw [he] at hB
  rw [sum_sub_distrib, ← sum_div] at hB
  have hU : (∑ x : ZMod n, if x ^ 2 = 0 then 0 else (1 / 2 : ℝ)) ≤ ((n : ℝ) - 1) / 2 := by
    have herase := Finset.sum_erase_add (univ : Finset (ZMod n))
      (fun x => if x ^ 2 = 0 then 0 else (1 / 2 : ℝ)) (mem_univ (0 : ZMod n))
    simp only [zero_pow (by decide : 2 ≠ 0), ite_true, add_zero] at herase
    rw [← herase]
    calc
      _ ≤ ∑ x ∈ (univ : Finset (ZMod n)).erase 0, (1 / 2 : ℝ) := by
        apply sum_le_sum
        intro x hx
        split_ifs <;> norm_num
      _ = _ := by simp [card_erase_of_mem, Nat.cast_sub hn1]; ring
  have hR : (∑ x : ZMod n, ((x ^ 2).val : ℝ)) / n ≤ ((n : ℝ) - 1) / 2 := by linarith
  have hmul := (div_le_iff₀ hn).mp hR
  have hfinal : 2 * (∑ x : ZMod n, ((x ^ 2).val : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  exact_mod_cast hfinal

lemma sum_mod_sq_bound (n : ℕ) [NeZero n] :
    2 * (∑ k ∈ range n, k ^ 2 % n) ≤ n * (n - 1) := by
  have h := square_residue_sum_bound n
  have he : (∑ x : ZMod n, (x ^ 2).val) = ∑ k ∈ range n, k ^ 2 % n := by
    rw [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv]
    change (∑ i : Fin n, ((ZMod.finEquiv n i) ^ 2).val) = _
    simp_rw [finEquiv_nat, ← Nat.cast_pow, ZMod.val_natCast]
    exact Fin.sum_univ_eq_sum_range (fun k => k ^ 2 % n) n
  rw [he] at h
  exact h

end QuadraticBias

open Finset

/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}$.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 :=
by
  letI : NeZero n := ⟨by omega⟩
  have hb := QuadraticBias.sum_mod_sq_bound n
  change 2 * A048153 n ≤ n * (n - 1) at hb
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  have h₁ : n - 1 + 1 = n := Nat.sub_add_cancel h
  have hn₂ : 1 ≤ n ^ 2 := by nlinarith
  have h₂ : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel hn₂
  nlinarith

theorem oeis_48153_conjecture_0.disproof : ¬ (type_of% @oeis_48153_conjecture_0) := sorry
