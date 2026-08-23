import FormalConjectures.Util.ProblemImports

open Nat

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

open ArithmeticFunction Finset

def Bfun : ArithmeticFunction ℕ := sigma 1 * zeta

lemma Bfun_apply (n : ℕ) : Bfun n = ∑ d ∈ divisors n, sigma 1 d := by
  rw [Bfun, mul_zeta_apply]

lemma a_eq_two_sigma_sub_B (n : ℕ) :
    a n = (2 : ℤ) * sigma 1 n - Bfun n := by
  unfold a
  rw [sum_sub_distrib, Bfun_apply]
  have h : ∑ d ∈ n.divisors, (2 * d : ℤ) = (2 : ℤ) * ∑ d ∈ n.divisors, (d : ℤ) := by
    simp [mul_sum]
  rw [h, ← Nat.cast_sum, ← sigma_one_apply, Nat.cast_sum]

lemma isMultiplicative_Bfun : IsMultiplicative Bfun :=
  isMultiplicative_sigma.mul isMultiplicative_zeta

lemma Bfun_mul {m n : ℕ} (h : Coprime m n) : Bfun (m * n) = Bfun m * Bfun n :=
  isMultiplicative_Bfun.map_mul_of_coprime h

lemma sigma_mul_coprime {m n : ℕ} (h : Coprime m n) :
    sigma 1 (m * n) = sigma 1 m * sigma 1 n :=
  isMultiplicative_sigma.map_mul_of_coprime h

lemma sigma_prime_eq {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [sum_range_succ]
  ac_rfl

lemma Bfun_prime_eq {p : ℕ} (hp : p.Prime) : Bfun p = p + 2 := by
  rw [Bfun_apply, hp.divisors, sum_pair (Ne.symm hp.ne_one)]
  rw [sigma_one, sigma_prime_eq hp]
  omega

lemma sigma_two_pow (k : ℕ) : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow prime_two]
  rw [Nat.geomSum_eq (by decide : 2 ≤ 2)]
  simp

lemma Bfun_one : Bfun 1 = 1 := by
  rw [Bfun_apply]; simp [divisors_one, sigma_one]

lemma divisors_two_pow_succ (k : ℕ) :
    divisors (2 ^ (k + 1)) = insert (2 ^ (k + 1)) (divisors (2 ^ k)) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∣ 2 ^ (k + 1) := dvd_of_mem_divisors hx
    obtain ⟨j, hj, rfl⟩ := (dvd_prime_pow prime_two).mp hx'
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simp
    · simp only [mem_insert]
      right
      exact mem_divisors.mpr ⟨(dvd_prime_pow prime_two).mpr ⟨j, Nat.lt_succ_iff.mp hlt, rfl⟩,
        pow_ne_zero _ (by decide)⟩
  · intro hx
    simp only [mem_insert] at hx
    rcases hx with rfl | hx
    · exact mem_divisors_self _ (pow_ne_zero _ (by decide))
    · have : x ∣ 2 ^ k := dvd_of_mem_divisors hx
      exact mem_divisors.mpr ⟨this.trans (pow_dvd_pow _ (Nat.le_succ k)),
        pow_ne_zero _ (by decide)⟩

lemma two_pow_succ_not_mem (k : ℕ) : 2 ^ (k + 1) ∉ divisors (2 ^ k) := by
  intro h
  have : 2 ^ (k + 1) ∣ 2 ^ k := dvd_of_mem_divisors h
  have : k + 1 ≤ k := (pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp this
  omega

lemma k_add_three_le_two_pow (k : ℕ) : k + 3 ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 + 3 = k + 3 + 1 := by omega
      _ ≤ 2 ^ (k + 2) + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ (k + 2) + 2 ^ (k + 2) := by
        have : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
        exact Nat.add_le_add_left this _
      _ = 2 * 2 ^ (k + 2) := by ring
      _ = 2 ^ (k + 3) := by ring

lemma Bfun_two_pow (k : ℕ) : Bfun (2 ^ k) = 2 ^ (k + 2) - k - 3 := by
  induction k with
  | zero =>
    simp [Bfun_one]
  | succ k ih =>
    have hsum : Bfun (2 ^ (k + 1)) = Bfun (2 ^ k) + sigma 1 (2 ^ (k + 1)) := by
      rw [Bfun_apply, Bfun_apply, divisors_two_pow_succ, sum_insert (two_pow_succ_not_mem k)]
      ac_rfl
    rw [hsum, ih, sigma_two_pow (k + 1)]
    set A := 2 ^ (k + 2) with hA
    have hk3 : k + 3 ≤ A := by rw [hA]; exact k_add_three_le_two_pow k
    have h1 : 1 ≤ A := by rw [hA]; exact Nat.one_le_two_pow
    have : A - k - 3 + (A - 1) = 2 * A - k - 4 := by omega
    have hR : 2 ^ (k + 1 + 2) - (k + 1) - 3 = 2 * A - k - 4 := by
      have : 2 ^ (k + 1 + 2) = 2 * A := by rw [hA]; ring
      rw [this]
      have : k + 1 + 3 ≤ 2 * A := by
        have := k_add_three_le_two_pow (k + 1)
        rw [hA]
        convert this using 1
        ring
      omega
    rw [this, hR]

lemma prime_4409 : Nat.Prime 4409 := by norm_num

lemma prime_458009 : Nat.Prime 458009 := by norm_num

lemma coprime_two_pow_4409 : Coprime (2 ^ 14) 4409 := by
  rw [Nat.coprime_pow_left_iff (by decide : 0 < 14)]
  exact (coprime_primes prime_two prime_4409).mpr (by decide)

lemma coprime_two_pow_mul_4409_458009 : Coprime (2 ^ 14 * 4409) 458009 := by
  rw [coprime_mul_iff_left]
  refine ⟨?_, (coprime_primes prime_4409 prime_458009).mpr (by decide)⟩
  rw [Nat.coprime_pow_left_iff (by decide : 0 < 14)]
  exact (coprime_primes prime_two prime_458009).mpr (by decide)

lemma a_counterexample : a (2 ^ 14 * 4409 * 458009) = 1 := by
  rw [a_eq_two_sigma_sub_B]
  rw [sigma_mul_coprime coprime_two_pow_mul_4409_458009,
    Bfun_mul coprime_two_pow_mul_4409_458009]
  rw [sigma_mul_coprime coprime_two_pow_4409, Bfun_mul coprime_two_pow_4409]
  rw [sigma_two_pow, Bfun_two_pow, sigma_prime_eq prime_4409, sigma_prime_eq prime_458009,
    Bfun_prime_eq prime_4409, Bfun_prime_eq prime_458009]
  norm_num

/-- The OEIS A296075 conjecture is false: `a(2^14 * 4409 * 458009) = 1`
    with this argument distinct from `1` and `12`. -/
theorem oeis_296075_conjecture_0.disproof :
    ¬ ∀ n : ℕ, a n = 1 ↔ n = 1 ∨ n = 12 := by
  intro h
  have hiff := h (2 ^ 14 * 4409 * 458009)
  have ha : a (2 ^ 14 * 4409 * 458009) = 1 := a_counterexample
  have : 2 ^ 14 * 4409 * 458009 = 1 ∨ 2 ^ 14 * 4409 * 458009 = 12 := hiff.mp ha
  revert this
  decide

