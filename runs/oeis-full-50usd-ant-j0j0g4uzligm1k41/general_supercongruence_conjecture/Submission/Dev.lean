import FormalConjectures.Util.ProblemImports

open Nat BigOperators

namespace Dev

open PowerSeries

/-- multinomial coefficient c_m(k) = (mk)!/(k!)^m as a rational. -/
noncomputable def cq (m k : ℕ) : ℚ := ((m * k).factorial / (k.factorial ^ m) : ℕ)

/-- The "log-derivative" series C(x) = Σ_{j≥1} c_m(j) x^{j-1}, i.e. coeff n is c_m(n+1). -/
noncomputable def Cm (m : ℕ) : ℚ⟦X⟧ := mk fun n => cq m (n + 1)

/-- The recursively-defined coefficient sequence of A_m: a_0 = 1,
    n a_n = Σ_{j=1}^n c_j a_{n-j}. -/
noncomputable def arec (m : ℕ) : ℕ → ℚ
  | 0 => 1
  | (n+1) => (∑ j ∈ Finset.range (n+1), cq m (j+1) * arec m (n - j)) / (n+1)

/-- The power series A_m. -/
noncomputable def Am (m : ℕ) : ℚ⟦X⟧ := mk (arec m)

@[simp] theorem coeff_Am (m n : ℕ) : coeff n (Am m) = arec m n := coeff_mk _ _

@[simp] theorem arec_zero (m : ℕ) : arec m 0 = 1 := by rw [arec]

theorem arec_succ (m n : ℕ) :
    arec m (n+1) = (∑ j ∈ Finset.range (n+1), cq m (j+1) * arec m (n - j)) / (n+1) := by
  rw [arec]

@[simp] theorem constantCoeff_Am (m : ℕ) : constantCoeff (Am m) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Am, arec_zero]

theorem cq_nonneg (m k : ℕ) : 0 ≤ cq m k := by unfold cq; exact_mod_cast Nat.zero_le _

/-- `0 ≤ [x^n] A_m` (hence `b_m ≥ 0`, consistent with `b_m_int : ℕ`). -/
theorem arec_nonneg (m n : ℕ) : 0 ≤ arec m n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [arec_zero]; norm_num
    | (k+1) =>
      rw [arec_succ]
      apply div_nonneg _ (by positivity)
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (cq_nonneg _ _) (ih (k - j) (by omega))

/-- The defining ODE: `A' = C · A`. -/
theorem derivative_Am (m : ℕ) : d⁄dX ℚ (Am m) = Cm m * Am m := by
  ext n
  rw [coeff_derivative, coeff_Am, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [arec_succ]
  rw [div_mul_cancel₀ _ (by exact_mod_cast hn1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Cm, coeff_mk, coeff_Am]

/-- The ODE for powers: `(A^n)' = n · C · A^n`. -/
theorem derivative_Am_pow (m n : ℕ) :
    d⁄dX ℚ ((Am m)^n) = n • (Cm m * (Am m)^n) := by
  rw [Derivation.leibniz_pow, derivative_Am]
  cases n with
  | zero => simp
  | succ k =>
    congr 1
    rw [Nat.succ_sub_one, smul_eq_mul]
    ring

@[simp] theorem coeff_zero_Am_pow (m n : ℕ) : coeff 0 ((Am m)^n) = 1 := by
  rw [coeff_zero_eq_constantCoeff, map_pow, constantCoeff_Am, one_pow]

/-- Coefficient recurrence for `A^n`: `(k+1) · [x^{k+1}]A^n = n · Σ_{i≤k} c(i+1) · [x^{k-i}]A^n`. -/
theorem coeff_Am_pow_succ (m n k : ℕ) :
    (coeff (k+1) ((Am m)^n)) * ((k : ℚ)+1) =
      n * (∑ i ∈ Finset.range (k+1), cq m (i+1) * coeff (k - i) ((Am m)^n)) := by
  have h := congrArg (coeff k) (derivative_Am_pow m n)
  rw [coeff_derivative, map_nsmul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, nsmul_eq_mul] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Cm, coeff_mk]

/-! ### The coefficient factors as a product of binomials

`c_m(k) = (mk)!/(k!)^m` satisfies `c_{m+1}(k) = c_m(k) · C((m+1)k, k)`, hence
`c_m(k) = ∏_{j=2}^m C(jk,k)`. This reduces the multinomial congruences to binomial ones. -/

/-- `(k!)^m ∣ (mk)!`. -/
theorem factorial_pow_dvd (m k : ℕ) : (k.factorial)^m ∣ (m*k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (k.factorial)^m * k.factorial ∣ (m*k).factorial * k.factorial :=
      mul_dvd_mul_right ih _
    have h2 : (m*k).factorial * k.factorial ∣ ((m+1)*k).factorial := by
      have he : (m+1)*k = m*k + k := by ring
      rw [he]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    calc (k.factorial)^(m+1) = (k.factorial)^m * k.factorial := by rw [pow_succ]
      _ ∣ (m*k).factorial * k.factorial := h1
      _ ∣ ((m+1)*k).factorial := h2

/-- Natural-number version of `c_m(k)`. -/
def cn (m k : ℕ) : ℕ := (m*k).factorial / (k.factorial)^m

/-- The multiplicative recurrence `c_{m+1}(k) = c_m(k) · C((m+1)k, k)`. -/
theorem cn_succ (m k : ℕ) : cn (m+1) k = cn m k * Nat.choose ((m+1)*k) k := by
  have hkle : k ≤ (m+1)*k := Nat.le_mul_of_pos_left k (by omega)
  have hsub : (m+1)*k - k = m*k := by rw [Nat.succ_mul]; omega
  have hchoose : Nat.choose ((m+1)*k) k * k.factorial * (m*k).factorial = ((m+1)*k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hkle
    rw [hsub] at this; exact this
  have hkpos : 0 < k.factorial := k.factorial_pos
  have hdvd : (k.factorial)^m ∣ (m*k).factorial := factorial_pow_dvd m k
  unfold cn
  rw [← hchoose, pow_succ]
  rw [show Nat.choose ((m+1)*k) k * k.factorial * (m*k).factorial
        = k.factorial * (Nat.choose ((m+1)*k) k * (m*k).factorial) by ring,
      show (k.factorial)^m * k.factorial = k.factorial * (k.factorial)^m by ring]
  rw [Nat.mul_div_mul_left _ _ hkpos, Nat.mul_div_assoc _ hdvd, Nat.mul_comm]

@[simp] theorem cn_zero (k : ℕ) : cn 0 k = 1 := by simp [cn]

/-- `c_1(k) = 1`. -/
@[simp] theorem cn_one (k : ℕ) : cn 1 k = 1 := by
  rw [cn_succ, cn_zero, one_mul]; simp

/-- `c_2(k) = C(2k, k)` — validation that `c_m` matches the central binomial for `m = 2`. -/
theorem cn_two (k : ℕ) : cn 2 k = Nat.choose (2*k) k := by
  rw [cn_succ, cn_one, one_mul]

/-- The mod-`p` Dwork congruence `c_m(pk) ≡ c_m(k) (mod p)`, via Lucas' theorem
    applied to each binomial factor. -/
theorem cn_pk_modEq (p : ℕ) [Fact p.Prime] (m k : ℕ) :
    (cn m (p*k) : ℤ) ≡ (cn m k : ℤ) [ZMOD p] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [cn_succ, cn_succ]
    push_cast
    refine Int.ModEq.mul ih ?_
    have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
    have key : Nat.choose ((m+1)*(p*k)) (p*k) ≡
        Nat.choose ((m+1)*k) k [ZMOD p] := by
      have h := Choose.choose_modEq_choose_mod_mul_choose_div
        (n := (m+1)*(p*k)) (k := p*k) (p := p)
      have e1 : (m+1)*(p*k) % p = 0 := by
        rw [show (m+1)*(p*k) = p*((m+1)*k) by ring]; exact Nat.mul_mod_right _ _
      have e2 : (p*k) % p = 0 := Nat.mul_mod_right _ _
      have e3 : (m+1)*(p*k) / p = (m+1)*k := by
        rw [show (m+1)*(p*k) = p*((m+1)*k) by ring]; exact Nat.mul_div_cancel_left _ hp0
      have e4 : (p*k) / p = k := Nat.mul_div_cancel_left _ hp0
      rw [e1, e2, e3, e4] at h
      simpa using h
    exact_mod_cast key

/-- Integer form of the mod-`p` Dwork congruence: `p ∣ c_m(pk) - c_m(k)`.
    (The `p`-level necklace / Witt integrality fragment.) -/
theorem dvd_cn_pk_sub (p : ℕ) [Fact p.Prime] (m k : ℕ) :
    (p : ℤ) ∣ (cn m k : ℤ) - (cn m (p*k) : ℤ) :=
  Int.ModEq.dvd (cn_pk_modEq p m k)

/-- Bridge between the power-series coefficient `cq` and the arithmetic `cn`. -/
theorem cq_eq_cn (m k : ℕ) : cq m k = (cn m k : ℚ) := rfl

/-- `c_m(k) > 0`. -/
theorem cn_pos (m k : ℕ) : 0 < cn m k :=
  Nat.div_pos (Nat.le_of_dvd (m*k).factorial_pos (factorial_pow_dvd m k))
    (pow_pos k.factorial_pos m)

/-- Coefficient extraction: `[x^k] (X+1)^n = C(n,k)` in any commutative semiring. -/
theorem coeff_X_add_one_pow (R : Type*) [CommSemiring R] (n k : ℕ) :
    ((Polynomial.X + 1 : Polynomial R)^n).coeff k = (n.choose k : R) := by
  rw [add_pow, Polynomial.finset_sum_coeff]
  simp only [one_pow, mul_one, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C,
    Polynomial.coeff_X_pow, boole_mul]
  rw [Finset.sum_ite_eq (Finset.range (n + 1)) k (fun m => (n.choose m : R))]
  simp only [Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- Frobenius on polynomials: `(1 + X)^p = 1 + X^p` in `(ZMod p)[X]`.
    A kernel ingredient for the mod-`p²` Dwork congruence. -/
theorem frobenius_add_X (p : ℕ) [Fact p.Prime] :
    ((1 : Polynomial (ZMod p)) + Polynomial.X)^p = 1 + Polynomial.X^p := by
  haveI : ExpChar (Polynomial (ZMod p)) p := ExpChar.prime (Fact.out (p := p.Prime))
  rw [add_pow_char, one_pow]

/-- Harmonic-sum building block: `Σ_{x ∈ ZMod p} x⁻¹ = 0` (via the involution `x ↦ x⁻¹`
    and `Σ x = 0`), an ingredient for the mod-`p²` Dwork congruence. -/
theorem sum_inv_zmod (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  have h2 : ∑ x : ZMod p, x = 0 := by
    have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1 (by rw [hc]; omega)
    simpa using this
  have hbij : Function.Bijective (fun x : ZMod p => x⁻¹) :=
    Function.Involutive.bijective (fun x => inv_inv x)
  calc ∑ x : ZMod p, x⁻¹
      = ∑ _y : ZMod p, (_y : ZMod p) :=
        Fintype.sum_bijective _ hbij (fun x => x⁻¹) (fun y => y) (fun x => rfl)
    _ = 0 := h2

/-- Iterated mod-`p` Dwork congruence: `c_m(p^a k) ≡ c_m(k) (mod p)`. -/
theorem cn_ppow_modEq (p : ℕ) [Fact p.Prime] (m a k : ℕ) :
    (cn m (p^a * k) : ℤ) ≡ (cn m k : ℤ) [ZMOD p] := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h := cn_pk_modEq p m (p^a * k)
    rw [show p * (p^a * k) = p^(a+1) * k by ring] at h
    exact h.trans ih

end Dev
