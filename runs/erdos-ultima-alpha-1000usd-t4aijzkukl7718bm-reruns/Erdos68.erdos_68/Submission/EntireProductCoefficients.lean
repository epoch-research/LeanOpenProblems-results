import FormalConjecturesUtil

/-!
Integer factorial-scaled coefficients of finite Lambert pole products,
and their prime-index congruences. Auxiliary arithmetic only.
-/
namespace EntireProductCoefficients

open Polynomial

def shiftCoeff (d : ℕ) (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  if d ≤ n then (n.choose d : ℤ) * u (n-d) else 0

def productCoeff : ℕ → ℕ → ℤ
  | 0, n => if n=0 then 1 else 0
  | K+1, n => productCoeff K n - shiftCoeff (K+2) (productCoeff K) n

def markedCoeff : ℕ → ℕ → ℤ
  | 0, _ => 0
  | K+1, n => markedCoeff K n - shiftCoeff (K+2) (markedCoeff K) n +
      shiftCoeff (K+2) (productCoeff K) n

noncomputable def shift (d : ℕ) (P : ℚ[X]) : ℚ[X] :=
  C (1 / (d.factorial : ℚ)) * (X^d * P)

noncomputable def product : ℕ → ℚ[X]
  | 0 => 1
  | K+1 => product K - shift (K+2) (product K)

noncomputable def marked : ℕ → ℚ[X]
  | 0 => 0
  | K+1 => marked K - shift (K+2) (marked K) + shift (K+2) (product K)

lemma scaled_shift (d : ℕ) (P : ℚ[X]) (u : ℕ → ℤ)
    (hu : ∀ n, (n.factorial : ℚ) * P.coeff n = u n) (n : ℕ) :
    (n.factorial : ℚ) * (shift d P).coeff n = shiftCoeff d u n := by
  simp only [shift, coeff_C_mul, coeff_X_pow_mul', shiftCoeff]
  by_cases hd : d ≤ n
  · rw [if_pos hd, if_pos hd]
    have he : (n.choose d : ℚ) * d.factorial * (n-d).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hd
    have hdf : (d.factorial : ℚ) ≠ 0 := by positivity
    rw [← he]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [← hu]
    field_simp
  · simp [hd]

lemma product_coeff (K n : ℕ) :
    (n.factorial : ℚ) * (product K).coeff n = productCoeff K n := by
  induction K generalizing n with
  | zero =>
    cases n with
    | zero => simp [product, productCoeff]
    | succ n => simp [product, productCoeff, coeff_one]
  | succ K ih =>
    rw [product, coeff_sub, mul_sub, ih, scaled_shift _ _ _ ih]
    simp [productCoeff]

lemma marked_coeff (K n : ℕ) :
    (n.factorial : ℚ) * (marked K).coeff n = markedCoeff K n := by
  induction K generalizing n with
  | zero => simp [marked, markedCoeff]
  | succ K ih =>
    rw [marked, coeff_add, coeff_sub, mul_add, mul_sub, ih,
      scaled_shift _ _ _ ih, scaled_shift _ _ _ (product_coeff K)]
    simp [markedCoeff]

lemma product_eq_prod (K : ℕ) :
    product K = ∏ k ∈ Finset.range K,
      (1 - C (1 / ((k+2).factorial : ℚ)) * X^(k+2)) := by
  induction K with
  | zero => simp [product]
  | succ K ih =>
    rw [product, Finset.prod_range_succ, ← ih]
    simp only [shift]
    ring

@[simp] lemma productCoeff_zero (K : ℕ) : productCoeff K 0 = 1 := by
  induction K with
  | zero => simp [productCoeff]
  | succ K ih => simp [productCoeff, shiftCoeff, ih]

@[simp] lemma markedCoeff_zero (K : ℕ) : markedCoeff K 0 = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simp [markedCoeff, shiftCoeff, ih]

lemma prime_shift_dvd (p d : ℕ) (hp : p.Prime) (hd0 : d ≠ 0) (hd : d < p)
    (u : ℕ → ℤ) : (p : ℤ) ∣ shiftCoeff d u p := by
  rw [shiftCoeff, if_pos hd.le]
  apply dvd_mul_of_dvd_left
  exact_mod_cast hp.dvd_choose_self hd0 hd

lemma before_prime (p K : ℕ) (hp : p.Prime) (hK : K+1 < p) :
    (p : ℤ) ∣ productCoeff K p ∧ (p : ℤ) ∣ markedCoeff K p := by
  induction K with
  | zero => simp [productCoeff, markedCoeff, hp.ne_zero]
  | succ K ih =>
    have hh := ih (by omega)
    have hd : K+2 < p := by omega
    have hprod := prime_shift_dvd p (K+2) hp (by omega) hd (productCoeff K)
    have hmark := prime_shift_dvd p (K+2) hp (by omega) hd (markedCoeff K)
    exact ⟨dvd_sub hh.1 hprod, dvd_add (dvd_sub hh.2 hmark) hprod⟩

/-- The coefficient stabilizes once every factor of degree at most n is present. -/
def h (n : ℕ) : ℤ := productCoeff n n

def k (n : ℕ) : ℤ := markedCoeff n n

@[simp] lemma h_zero : h 0 = 1 := by simp [h]
@[simp] lemma k_zero : k 0 = 0 := rfl

lemma at_prime (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ h p + 1 ∧ (p : ℤ) ∣ k p - 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r+2 := ⟨p-2, by have := hp.two_le; omega⟩
  have hh := before_prime (r+2) r hp (by omega)
  simp only [h, k, productCoeff, markedCoeff, shiftCoeff,
    show ¬r+1+2 ≤ r+2 by omega, if_false, sub_zero, add_zero,
    show r+2 ≤ r+2 by omega, if_true, Nat.choose_self, Nat.sub_self,
    Int.natCast_one, one_mul, productCoeff_zero, markedCoeff_zero] at *
  constructor
  · simpa using hh.1
  · simpa using hh.2

lemma stable_coefficients (n K : ℕ) (hK : n ≤ K) :
    productCoeff K n = h n ∧ markedCoeff K n = k n := by
  induction K, hK using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ K hK ih =>
    simp only [productCoeff, markedCoeff, shiftCoeff,
      show ¬K+2 ≤ n by omega, if_false, sub_zero, add_zero]
    exact ih

/-- The marked finite product is the ordinary product times the finite
reciprocal-factorial-minus-one sum, at the evaluation point one. -/
lemma marked_eval_one (K : ℕ) :
    (marked K).eval 1 = (product K).eval 1 *
      (∑ i ∈ Finset.range K, 1 / ((i+2).factorial - 1 : ℚ)) := by
  induction K with
  | zero => simp [marked]
  | succ K ih =>
    have hf : (2 : ℕ) ≤ (K+2).factorial := by
      simpa using Nat.factorial_le (show 2 ≤ K+2 by omega)
    have hfQ : (2 : ℚ) ≤ (K+2).factorial := by exact_mod_cast hf
    have h₀ : ((K+2).factorial : ℚ) ≠ 0 := by positivity
    have h₁ : ((K+2).factorial : ℚ)-1 ≠ 0 := by linarith
    simp only [marked, product, shift, eval_add, eval_sub, eval_mul,
      eval_C, eval_pow, eval_X, one_pow, one_mul, Finset.sum_range_succ]
    rw [ih]
    field_simp

/-- The coefficients of (b*K-a*H)/(1-z), in exponential normalization. -/
def quotient (a b : ℤ) : ℕ → ℤ
  | 0 => -a
  | n+1 => (n+1 : ℤ) * quotient a b n + b * k (n+1) - a * h (n+1)

noncomputable def series (u : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (u n : ℚ) / (n.factorial : ℚ))

lemma quotient_identity (a b : ℤ) :
    (1 - PowerSeries.X) * series (quotient a b) =
      PowerSeries.C (b : ℚ) * series k - PowerSeries.C (a : ℚ) * series h := by
  ext n
  rw [sub_mul, one_mul]
  cases n with
  | zero => simp [series, quotient]
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
      series, PowerSeries.coeff_mk]
    have hn : (n+1 : ℚ) ≠ 0 := by positivity
    have hf : (n.factorial : ℚ) ≠ 0 := by positivity
    simp only [quotient, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Int.cast_one, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
    ring

lemma quotient_prime (a b : ℤ) (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ quotient a b p - (a+b) := by
  obtain ⟨n, rfl⟩ : ∃ n, p=n+1 := ⟨p-1, by have := hp.pos; omega⟩
  have hp' := at_prime (n+1) hp
  have h₁ : (n+1 : ℤ) ∣ (n+1 : ℤ) * quotient a b n := dvd_mul_right _ _
  have h₂ := dvd_mul_of_dvd_right hp'.2 b
  have h₃ := dvd_mul_of_dvd_right hp'.1 a
  convert dvd_sub (dvd_add h₁ h₂) h₃ using 1
  simp only [quotient]
  ring

lemma quotient_prime_ne_zero (a b : ℤ) (p : ℕ) (hp : p.Prime)
    (hab : 0 < a+b) (hbound : a+b < (p : ℤ)) : quotient a b p ≠ 0 := by
  intro hz
  have hd := quotient_prime a b p hp
  rw [hz, zero_sub] at hd
  have he := Int.eq_zero_of_abs_lt_dvd (dvd_neg.mp hd)
    (show |a+b| < (p : ℤ) by simpa [abs_of_pos hab] using hbound)
  omega

#print axioms product_coeff
#print axioms marked_coeff
#print axioms marked_eval_one
#print axioms stable_coefficients
#print axioms at_prime
#print axioms quotient_identity
#print axioms quotient_prime
#print axioms quotient_prime_ne_zero

end EntireProductCoefficients
