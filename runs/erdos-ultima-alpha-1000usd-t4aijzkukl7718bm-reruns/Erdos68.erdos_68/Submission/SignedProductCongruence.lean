import FormalConjecturesUtil

/-!
# Signed denominator products and their affine congruences

Auxiliary arithmetic for Erdős 68. These congruences alone do not prove
irrationality: the corresponding cleared real tails need not be small.
-/

namespace SignedProductCongruence

/-- The product of `1 - k!` for `2 ≤ k ≤ n + 1`. -/
def product : ℕ → ℤ
  | 0 => 1
  | n + 1 => (1 - (n + 2).factorial) * product n

/-- The numerator obtained by clearing the first `n` summands with `product n`. -/
def numerator : ℕ → ℤ
  | 0 => 0
  | n + 1 => (1 - (n + 2).factorial) * numerator n - product n

def adjusted (n : ℕ) : ℤ := numerator n + n * product n

def cleared (p q : ℤ) (n : ℕ) : ℤ := p * product n - q * numerator n

lemma product_step (n : ℕ) :
    product (n + 1) - product n = -(n + 2).factorial * product n := by
  rw [product]
  ring

lemma adjusted_step (n : ℕ) :
    adjusted (n + 1) - adjusted n =
      -(n + 2).factorial * (numerator n + (n + 1 : ℤ) * product n) := by
  simp only [adjusted, numerator, product, Nat.cast_add, Nat.cast_one]
  ring

lemma factorial_dvd_step {B n : ℕ} (h : B ≤ n + 2) :
    (B.factorial : ℤ) ∣ product (n + 1) - product n := by
  rw [product_step]
  have hd : (B.factorial : ℤ) ∣ ((n + 2).factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial h
  exact dvd_mul_of_dvd_left (dvd_neg.mpr hd) _

lemma factorial_dvd_adjusted_step {B n : ℕ} (h : B ≤ n + 2) :
    (B.factorial : ℤ) ∣ adjusted (n + 1) - adjusted n := by
  rw [adjusted_step]
  have hd : (B.factorial : ℤ) ∣ ((n + 2).factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial h
  exact dvd_mul_of_dvd_left (dvd_neg.mpr hd) _

lemma product_congruence {B N n : ℕ} (hB : B ≤ N + 2) (hn : N ≤ n) :
    (B.factorial : ℤ) ∣ product n - product N := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := factorial_dvd_step (show B ≤ n + 2 by omega)
    convert dvd_add hs ih using 1
    ring

lemma adjusted_congruence {B N n : ℕ} (hB : B ≤ N + 2) (hn : N ≤ n) :
    (B.factorial : ℤ) ∣ adjusted n - adjusted N := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := factorial_dvd_adjusted_step (show B ≤ n + 2 by omega)
    convert dvd_add hs ih using 1
    ring

/-- For any candidate numerator and denominator, the cleared numerators obey
an affine congruence in the cutoff. No rationality hypothesis is used here. -/
theorem cleared_affine_congruence (p q : ℤ) {B N n : ℕ}
    (hB : B ≤ N + 2) (hn : N ≤ n) :
    (B.factorial : ℤ) ∣
      cleared p q n - cleared p q N - q * ((n : ℤ) - N) * product N := by
  have hp := product_congruence hB hn
  have ha := adjusted_congruence hB hn
  have h := dvd_sub (dvd_mul_of_dvd_right hp (p + q * n))
    (dvd_mul_of_dvd_right ha q)
  convert h using 1
  simp only [cleared, adjusted]
  ring

lemma cast_product_mul_partial (n : ℕ) :
    (product n : ℝ) *
      (∑ k ∈ Finset.range n, 1 / ((k + 2).factorial - 1 : ℝ)) = numerator n := by
  induction n with
  | zero => simp [product, numerator]
  | succ n ih =>
    have hf : (2 : ℕ) ≤ (n + 2).factorial := by
      simpa using Nat.factorial_le (show 2 ≤ n + 2 by omega)
    have hd : ((n + 2).factorial : ℝ) - 1 ≠ 0 := by
      have hf' : (2 : ℝ) ≤ (n + 2).factorial := by exact_mod_cast hf
      linarith
    rw [Finset.sum_range_succ]
    simp only [product, numerator, Int.cast_mul, Int.cast_sub, Int.cast_one,
      Int.cast_natCast]
    rw [mul_add, mul_assoc, ih]
    field_simp
    ring

/-- Under a putative rational value, `cleared` is exactly the scaled real tail.
The scaling is the full product, not a single factorial. -/
theorem cleared_eq_scaled_tail (x : ℝ) (p q : ℤ)
    (hx : (q : ℝ) * x = p) (n : ℕ) :
    (cleared p q n : ℝ) = (q : ℝ) * product n *
      (x - ∑ k ∈ Finset.range n, 1 / ((k + 2).factorial - 1 : ℝ)) := by
  have hn := cast_product_mul_partial n
  simp only [cleared, Int.cast_sub, Int.cast_mul]
  rw [← hx, ← hn]
  ring

#print axioms cleared_affine_congruence
#print axioms cleared_eq_scaled_tail

end SignedProductCongruence
