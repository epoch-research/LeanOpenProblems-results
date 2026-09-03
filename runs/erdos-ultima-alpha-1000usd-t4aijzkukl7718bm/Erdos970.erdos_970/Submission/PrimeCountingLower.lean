import FormalConjecturesUtil

/-! Elementary lower bounds for the prime counting function, to support the
quantitative sieve investigation. These are not Jacobsthal bounds. -/
namespace Erdos970.PrimeCountingLower

lemma two_pow_le_centralBinom (n : ℕ) : 2 ^ n ≤ n.centralBinom := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid := Nat.succ_mul_centralBinom_succ n
    have hstep : 2 * n.centralBinom ≤ (n + 1).centralBinom := by nlinarith
    rw [pow_succ]
    nlinarith

lemma centralBinom_le_primeCounting_pow (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ (2 * n).primeCounting := by
  classical
  let P := (2 * n + 1).primesBelow
  have heq : n.centralBinom = ∏ p ∈ P, p ^ n.centralBinom.factorization p := by
    conv_lhs => rw [← Nat.prod_pow_factorization_centralBinom n]
    symm
    dsimp only [P, Nat.primesBelow]
    apply Finset.prod_filter_of_ne
    intro p hp hne
    by_contra hnp
    exact hne (by rw [Nat.factorization_eq_zero_of_not_prime _ hnp, pow_zero])
  have hcard : P.card = (2 * n).primeCounting := by
    simp only [P, Nat.primesBelow, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [heq, ← hcard, ← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)

/-- A logarithmic lower bound at even arguments. -/
theorem even_log_bound (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 2 ≤ ((2 * n).primeCounting : ℝ) * Real.log (2 * n : ℕ) := by
  have he := (two_pow_le_centralBinom n).trans (centralBinom_le_primeCounting_pow n hn)
  have heR : (2 : ℝ) ^ n ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n).primeCounting := by exact_mod_cast he
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n) heR
  simpa only [Real.log_pow] using hl

/-- An elementary Chebyshev-type lower bound, with a convenient explicit constant. -/
theorem log_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.log 2 * (n : ℝ) ≤ 4 * (n.primeCounting : ℝ) * Real.log n := by
  have hn2 : 0 < n / 2 := by omega
  have he := even_log_bound (n / 2) hn2
  have hle : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hcount := Nat.monotone_primeCounting hle
  have hlog : Real.log ((2 * (n / 2) : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hle
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hupper : (((2 * (n / 2)).primeCounting : ℕ) : ℝ) * Real.log (2 * (n / 2) : ℕ) ≤
      (n.primeCounting : ℝ) * Real.log n :=
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hlogpos)
  have hfloor : n ≤ 4 * (n / 2) := by omega
  have hfloorR : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by exact_mod_cast hfloor
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

theorem lower_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.log 2 * (n : ℝ) / (4 * Real.log n) ≤ n.primeCounting := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (n : ℝ))).mpr
  nlinarith [log_bound n hn]

lemma primeCounting_nth (k : ℕ) :
    (Nat.nth Nat.Prime k).primeCounting = k + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  simp only [Nat.prime_nth_prime, if_true]
  exact congrArg (fun x => x + 1) (Nat.primeCounting'_nth_eq k)

lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

/-- A convenient preliminary bound for the enumerated primes (not for Jacobsthal's function). -/
theorem nth_prime_quadratic (k : ℕ) :
    (Nat.nth Nat.Prime k : ℝ) ≤ 256 * ((k : ℝ) + 1) ^ 2 := by
  let p := Nat.nth Nat.Prime k
  have hp := Nat.prime_nth_prime k
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := log_bound p hp.two_le
  rw [primeCounting_nth] at hlog
  push_cast at hlog
  have hsq := Real.sq_sqrt hpR.le
  have hspos := Real.sqrt_pos.mpr hpR
  have hlogroot := Real.log_le_sub_one_of_pos hspos
  rw [Real.log_sqrt hpR.le] at hlogroot
  have hhalf := mul_le_mul_of_nonneg_right half_le_log_two hpR.le
  have hlogweak : (p : ℝ) ≤ 8 * ((k : ℝ) + 1) * Real.log p := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hlogroot (by positivity : (0 : ℝ) ≤ 16 * ((k : ℝ) + 1))
  have hsbound : Real.sqrt p ≤ 16 * ((k : ℝ) + 1) := by nlinarith
  change (p : ℝ) ≤ _
  nlinarith

/-- An explicit logarithmic upper bound on the k-th prime, derived from the elementary
prime-counting lower bound. It does not bound the Jacobsthal function. -/
theorem nth_prime_mul_log (k : ℕ) :
    (Nat.nth Nat.Prime k : ℝ) ≤ 80 * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
  let p := Nat.nth Nat.Prime k
  have hp := Nat.prime_nth_prime k
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := log_bound p hp.two_le
  rw [primeCounting_nth] at hlog
  push_cast at hlog
  have hhalf := mul_le_mul_of_nonneg_right half_le_log_two hpR.le
  have hlogweak : (p : ℝ) ≤ 8 * ((k : ℝ) + 1) * Real.log p := by nlinarith
  have hlogp := Real.log_le_log hpR (nth_prime_quadratic k)
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, h256] at hlogp
  have hlog1 : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log ((k : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hlogp' : Real.log (p : ℝ) ≤ 10 * Real.log ((k : ℝ) + 2) := by
    norm_num at hlogp
    linarith
  have hprod := mul_le_mul_of_nonneg_left hlogp' (by positivity : (0 : ℝ) ≤ 8 * ((k : ℝ) + 1))
  change (p : ℝ) ≤ _
  nlinarith

#print axioms lower_bound
#print axioms nth_prime_mul_log
end Erdos970.PrimeCountingLower
