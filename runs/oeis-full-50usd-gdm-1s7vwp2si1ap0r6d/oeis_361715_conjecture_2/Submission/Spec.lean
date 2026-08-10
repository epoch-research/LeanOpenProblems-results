import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A361715: $$a(n) = \sum_{k = 0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}$$
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k


lemma factorization_choose_prime_pow_coprime {p n k : ℕ} (hp : Nat.Prime p) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) (hkp : ¬ p ∣ k) :
  ((p ^ n).choose k).factorization p = n := by
  rw [factorization_choose_prime_pow hp hkn hk0]
  have : k.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hkp
  rw [this, Nat.sub_zero]

lemma factorization_choose_prime_pow_coprime_sq {p n k : ℕ} (hp : Nat.Prime p) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) (hkp : ¬ p ∣ k) :
  (((p ^ n).choose k) ^ 2).factorization p = 2 * n := by
  rw [factorization_pow]
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  rw [factorization_choose_prime_pow_coprime hp hkn hk0 hkp]
  rfl

lemma choose_sq_divisible {p n k : ℕ} (hp : Nat.Prime p) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) (hkp : ¬ p ∣ k) :
  p ^ (2 * n) ∣ ((p ^ n).choose k) ^ 2 := by
  have h_ne : ((p ^ n).choose k) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    apply pos_iff_ne_zero.mp
    apply Nat.choose_pos
    exact hkn
  rw [hp.pow_dvd_iff_le_factorization h_ne]
  rw [factorization_choose_prime_pow_coprime_sq hp hkn hk0 hkp]

lemma coprime_summand_divisible {p n k : ℕ} (hp : Nat.Prime p) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) (hkp : ¬ p ∣ k) :
  p ^ (2 * n) ∣ ((p ^ n).choose k) ^ 2 * multichoose (p ^ n) k := by
  have h := choose_sq_divisible hp hkn hk0 hkp
  rw [multichoose_eq]
  exact dvd_mul_of_dvd_left h _

/-- Conjecture 2: for r >= 2, the supercongruence a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) holds for all primes p >= 5. -/
theorem oeis_361715_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  rcases r with _ | _ | k
  · omega
  · omega
  -- now r = k + 2
  have hp_pos : p > 0 := hp.pos
  have h_r_ge : k + 2 ≥ 2 := by omega
  -- The core of the supercongruence rests on the combination of coprime and divisible term estimations
  -- of the summation of choose(p^r, k)^2 * multichoose(p^r, k).
  -- Proving this completely from scratch requires advanced p-adic analysis.
  sorry


#print axioms oeis_361715_conjecture_2

