import FormalConjecturesUtil

/-!
# Uniform divisor bounds on polynomial-height ranges

For every fixed positive integer `k`, the `k`-th power of the divisor count is
at most a constant times `n`. Consequently, for fixed `K` and `M`, uniformly for
`n ≤ H^K`, eventually `M * n.divisors.card < H`. The proof separates the finitely
many primes below `2^k` from the other prime factors. No squarefree-gap assertion
is used.
-/

open Finset Filter

namespace DivisorPower

lemma succ_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ]
      omega

lemma exists_power_bound (k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ e : ℕ, (e + 1) ^ k ≤ C * 2 ^ e := by
  have hevent : ∀ᶠ e : ℕ in atTop, e ^ k ≤ 2 ^ e := by
    have hb := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
      (by norm_num : (1 : ℝ) < 2)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb] with e he
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (e : ℝ) ^ k by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ 2 ^ e by positivity), one_mul] at he
    exact_mod_cast he
  obtain ⟨e₀, he₀⟩ := eventually_atTop.mp hevent
  refine ⟨(e₀ + 1) ^ k + 2 ^ k, by positivity, ?_⟩
  intro e
  by_cases he : e ≤ e₀
  · calc
      (e + 1) ^ k ≤ (e₀ + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      _ ≤ (e₀ + 1) ^ k + 2 ^ k := Nat.le_add_right _ _
      _ ≤ ((e₀ + 1) ^ k + 2 ^ k) * 2 ^ e :=
        Nat.le_mul_of_pos_right _ (by positivity)
  · calc
      (e + 1) ^ k ≤ (2 * e) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * e ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * 2 ^ e := Nat.mul_le_mul_left _ (he₀ e (by omega))
      _ ≤ ((e₀ + 1) ^ k + 2 ^ k) * 2 ^ e := by gcongr; omega

/-- The divisor function has every positive integer power bounded linearly. -/
theorem exists_divisors_pow_le (k : ℕ) (hk : 0 < k) :
    ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, n.divisors.card ^ k ≤ D * n := by
  obtain ⟨C, hC, hCe⟩ := exists_power_bound k
  refine ⟨C ^ (2 ^ k), by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Nat.ne_of_gt hk]
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p + 1) ^ k ≤
        (if p < 2 ^ k then C else 1) * p ^ n.factorization p := by
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < 2 ^ k
    · simp only [if_pos hsmall]
      exact (hCe (n.factorization p)).trans
        (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hp2 _))
    · simp only [if_neg hsmall, one_mul]
      calc
        (n.factorization p + 1) ^ k ≤ (2 ^ n.factorization p) ^ k :=
          Nat.pow_le_pow_left (succ_le_two_pow _) k
        _ = (2 ^ k) ^ n.factorization p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ n.factorization p := Nat.pow_le_pow_left (by omega) _
  have hcount : (n.primeFactors.filter (fun p => p < 2 ^ k)).card ≤ 2 ^ k := by
    calc
      _ ≤ (range (2 ^ k)).card := by
        apply card_le_card
        intro p hp
        exact mem_range.mpr (mem_filter.mp hp).2
      _ = _ := card_range _
  have hconst : (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) ≤ C ^ (2 ^ k) := by
    calc
      (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) =
          ∏ _p ∈ n.primeFactors.filter (fun p => p < 2 ^ k), C := by
        rw [prod_filter]
      _ = C ^ (n.primeFactors.filter (fun p => p < 2 ^ k)).card := prod_const _
      _ ≤ C ^ (2 ^ k) := pow_le_pow_right₀ (by omega) hcount
  calc
    n.divisors.card ^ k = ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k := by
      rw [Nat.card_divisors hn, prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 2 ^ k then C else 1) * p ^ n.factorization p := prod_le_prod' hprime
    _ = (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) * n := by
      rw [prod_mul_distrib]
      congr 1
      simpa only [Finsupp.prod, Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn
    _ ≤ C ^ (2 ^ k) * n := Nat.mul_le_mul_right _ hconst

/-- A uniform, root-free sublinear divisor bound throughout a polynomial-height range. -/
theorem eventually_mul_card_divisors_lt (K M : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ n : ℕ, n ≤ H ^ K → M * n.divisors.card < H := by
  obtain ⟨D, _, hD⟩ := exists_divisors_pow_le (K + 1) (by omega)
  refine eventually_atTop.mpr ⟨M ^ (K + 1) * D + 1, ?_⟩
  intro H hH n hn
  have hHpos : 0 < H := by omega
  have hscale : M ^ (K + 1) * D < H := by omega
  have hpow : (M * n.divisors.card) ^ (K + 1) < H ^ (K + 1) := by
    calc
      (M * n.divisors.card) ^ (K + 1) = M ^ (K + 1) * n.divisors.card ^ (K + 1) :=
        mul_pow _ _ _
      _ ≤ M ^ (K + 1) * (D * n) := Nat.mul_le_mul_left _ (hD n)
      _ ≤ M ^ (K + 1) * (D * H ^ K) := by gcongr
      _ = (M ^ (K + 1) * D) * H ^ K := by ring
      _ < H * H ^ K := Nat.mul_lt_mul_of_pos_right hscale (pow_pos hHpos K)
      _ = H ^ (K + 1) := by rw [pow_succ]; ring
  exact (Nat.pow_lt_pow_iff_left (by omega : K + 1 ≠ 0)).mp hpow

#print axioms exists_divisors_pow_le
#print axioms eventually_mul_card_divisors_lt

end DivisorPower
