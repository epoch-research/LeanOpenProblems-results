import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Row sums of A340880.
$$a(n) = \sum_{k = 0}^{n-1} 2^{k(k+1)/2} \cdot \left( \prod_{j = k+1}^{n-1} (2^j - 1) \right)$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

/-- The fundamental recurrence: `a (n+1) = (2^n - 1) * a n + 2^(n(n+1)/2)`. -/
lemma a_succ (n : ℕ) :
    a (n + 1) = (2 ^ n - 1) * a n + 2 ^ Nat.choose (n + 1) 2 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Finset.prod_Ico_succ_top hk]
  ring

lemma a_one : a 1 = 1 := by
  simp [a]

lemma two_mul_choose (m : ℕ) : 2 * Nat.choose (m + 1) 2 = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ' (k + 1) 1, Nat.choose_one_right, Nat.mul_add, ih]
    ring

lemma choose_shift (n q : ℕ) :
    Nat.choose (n + 2 * q + 1) 2 = Nat.choose (n + 1) 2 + q * (2 * n + 2 * q + 1) := by
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  rw [Nat.mul_add, two_mul_choose, two_mul_choose]
  ring

lemma choose_base (q : ℕ) : Nat.choose (2 * q + 1) 2 = q * (2 * q + 1) := by
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  rw [two_mul_choose]
  ring

section OddPrime

variable (p : ℕ) [Fact p.Prime]

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  have h2le := (Fact.out : p.Prime).two_le
  omega

lemma two_pow_p_sub_one (hp2 : p ≠ 2) : (2 : ZMod p) ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod p hp2)

lemma two_pow_period (hp2 : p ≠ 2) : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
  rw [two_mul, pow_add, two_pow_p_sub_one p hp2, one_mul]

lemma two_pow_shift (hp2 : p ≠ 2) (n : ℕ) :
    (2 : ZMod p) ^ (n + 2 * (p - 1)) = 2 ^ n := by
  rw [pow_add, two_pow_period p hp2, mul_one]

lemma two_pow_choose_shift (hp2 : p ≠ 2) (n : ℕ) :
    (2 : ZMod p) ^ Nat.choose (n + 2 * (p - 1) + 1) 2 = 2 ^ Nat.choose (n + 1) 2 := by
  rw [choose_shift n (p - 1), pow_add, pow_mul, two_pow_p_sub_one p hp2, one_pow, mul_one]

/-- The recurrence, cast into `ZMod p`. -/
lemma a_succ_cast (n : ℕ) :
    ((a (n + 1) : ℕ) : ZMod p)
      = ((2 : ZMod p) ^ n - 1) * ((a n : ℕ) : ZMod p) + 2 ^ Nat.choose (n + 1) 2 := by
  rw [a_succ]
  push_cast [Nat.one_le_two_pow]
  ring

/-- Base case: `a (1 + 2*(p-1)) ≡ a 1 [MOD p]`.  Every summand except the last contains
the factor `2^(2*(p-1)) - 1 ≡ 0 (mod p)`; the last summand is
`2^((p-1)(2p-1)) ≡ 1 (mod p)`. -/
lemma a_base (hp2 : p ≠ 2) :
    ((a (1 + 2 * (p - 1)) : ℕ) : ZMod p) = ((a 1 : ℕ) : ZMod p) := by
  have hP : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := two_pow_period p hp2
  rw [a_one, Nat.cast_one]
  unfold a
  push_cast [Nat.one_le_two_pow]
  rw [Finset.sum_eq_single (2 * (p - 1))]
  · rw [show 1 + 2 * (p - 1) = 2 * (p - 1) + 1 from Nat.add_comm 1 _,
      Finset.Ico_self, Finset.prod_empty, mul_one, choose_base, pow_mul,
      two_pow_p_sub_one p hp2, one_pow]
  · intro b hb hbne
    rw [Finset.mem_range] at hb
    have hmem : 2 * (p - 1) ∈ Finset.Ico (b + 1) (1 + 2 * (p - 1)) := by
      rw [Finset.mem_Ico]; omega
    have hzero : (2 : ZMod p) ^ (2 * (p - 1)) - 1 = 0 := by
      rw [hP]; exact sub_self 1
    rw [Finset.prod_eq_zero hmem hzero, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end OddPrime

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · -- For p = 2 : a n is odd for all n ≥ 1.
    subst hp2
    have key : ∀ n, 1 ≤ n → a n % 2 = 1 := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rw [a_one]
      | succ m hm ih =>
        have h1 : (2 ^ m - 1) % 2 = 1 := by
          have hd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
          have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          omega
        have h2 : 2 ^ Nat.choose (m + 1) 2 % 2 = 0 := by
          have hpos : 0 < Nat.choose (m + 1) 2 := Nat.choose_pos (by omega)
          have hd : 2 ∣ 2 ^ Nat.choose (m + 1) 2 := dvd_pow_self 2 (by omega)
          omega
        rw [a_succ, Nat.add_mod, Nat.mul_mod, h1, ih, h2]
    intro n hn
    rw [key (n + 2 * (2 - 1)) (by omega), key n hn]
  · -- Odd primes: induction from n = 1 using the recurrence with periodic coefficients.
    intro n hn
    have key : ∀ m, 1 ≤ m →
        ((a (m + 2 * (p - 1)) : ℕ) : ZMod p) = ((a m : ℕ) : ZMod p) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact a_base p hp2
      | succ k hk ih =>
        have e : k + 1 + 2 * (p - 1) = k + 2 * (p - 1) + 1 := by omega
        rw [e, a_succ_cast, a_succ_cast, ih, two_pow_shift p hp2,
          two_pow_choose_shift p hp2]
    have h := key n hn
    rwa [ZMod.natCast_eq_natCast_iff'] at h
