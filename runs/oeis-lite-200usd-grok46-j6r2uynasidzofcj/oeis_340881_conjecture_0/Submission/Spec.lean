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

lemma a_zero : a 0 = 0 := by simp [a]

lemma a_one : a 1 = 1 := by
  simp [a, Nat.choose_succ_succ', Nat.choose_one_right]

/-- Recurrence: `a(n+1) = (2^n - 1) a(n) + 2^{n(n+1)/2}`. -/
lemma a_succ (n : ℕ) :
    a (n + 1) = (2 ^ n - 1) * a n + 2 ^ Nat.choose (n + 1) 2 := by
  unfold a
  rw [sum_range_succ]
  simp only [Ico_self, prod_empty, mul_one]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk' : k + 1 ≤ n := by
    rw [mem_range] at hk
    omega
  rw [prod_Ico_succ_top hk']
  ring

lemma choose_two_succ (n : ℕ) : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

lemma two_mul_choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [choose_two_succ, mul_add, ih, Nat.succ_sub_one]
    cases n with
    | zero => simp
    | succ n =>
      simp only [succ_sub_succ, Nat.sub_zero]
      ring

lemma choose_two_two_mul_p_sub_one (p : ℕ) (hp : 1 ≤ p) :
    Nat.choose (2 * p - 1) 2 = (2 * p - 1) * (p - 1) := by
  apply Nat.mul_left_cancel (Nat.succ_pos 1)
  rw [two_mul_choose_two]
  have : 2 * p - 1 - 1 = 2 * (p - 1) := by omega
  rw [this]
  ring

lemma choose_add_two_mul (n d : ℕ) :
    Nat.choose (n + 2 * d) 2 = Nat.choose n 2 + d * (2 * n + 2 * d - 1) := by
  have key : 2 * Nat.choose (n + 2 * d) 2 =
      2 * (Nat.choose n 2 + d * (2 * n + 2 * d - 1)) := by
    rw [two_mul_choose_two, mul_add, two_mul_choose_two]
    rcases n with _ | n
    · ring
    · have hsub : n + 1 + 2 * d - 1 = n + 2 * d := by omega
      have hsub' : 2 * (n + 1) + 2 * d - 1 = 2 * n + 2 * d + 1 := by omega
      rw [hsub, hsub', Nat.add_sub_cancel]
      ring
  omega

lemma natCast_two_pow_sub_one (j p : ℕ) :
    ((2 ^ j - 1 : ℕ) : ZMod p) = (2 : ZMod p) ^ j - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

lemma two_ne_zero_of_odd_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have : (p : ℕ) ∣ 2 := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact h
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
  exact hp2 this

lemma two_pow_p_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one (two_ne_zero_of_odd_prime hp2)

lemma two_pow_mul_p_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    (2 : ZMod p) ^ ((p - 1) * k) = 1 := by
  rw [pow_mul, two_pow_p_sub_one hp2, one_pow]

lemma two_pow_choose_period {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    (2 : ZMod p) ^ Nat.choose (k + 2 * (p - 1)) 2 =
      (2 : ZMod p) ^ Nat.choose k 2 := by
  rw [choose_add_two_mul, pow_add, two_pow_mul_p_sub_one hp2, mul_one]

lemma a_succ_cast (n p : ℕ) :
    (a (n + 1) : ZMod p) =
      ((2 : ZMod p) ^ n - 1) * (a n : ZMod p) +
        (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
  rw [a_succ, Nat.cast_add, Nat.cast_mul, natCast_two_pow_sub_one, Nat.cast_pow,
    Nat.cast_ofNat]

lemma a_two_mul_p_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (a (2 * p - 1) : ZMod p) = 1 := by
  have hppos : 1 ≤ p := Nat.Prime.one_le Fact.out
  have hT : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
  rw [hT, a]
  rw [sum_range_succ]
  have hlast :
      ((2 ^ Nat.choose (2 * (p - 1) + 1) 2 *
          ∏ j ∈ Ico (2 * (p - 1) + 1) (2 * (p - 1) + 1), (2 ^ j - 1) : ℕ) : ZMod p) = 1 := by
    simp only [Ico_self, prod_empty, mul_one]
    have hch : Nat.choose (2 * (p - 1) + 1) 2 = Nat.choose (2 * p - 1) 2 := by
      congr 1
      omega
    rw [Nat.cast_pow, Nat.cast_ofNat, hch, choose_two_two_mul_p_sub_one p hppos]
    rw [mul_comm, two_pow_mul_p_sub_one hp2]
  rw [Nat.cast_add, hlast, add_eq_right]
  rw [Nat.cast_sum]
  apply sum_eq_zero
  intro k hk
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod]
  refine mul_eq_zero_of_right _ (prod_eq_zero (i := 2 * (p - 1)) ?hmem ?hzero)
  · -- `2 * (p - 1)` belongs to `Ico (k + 1) (2 * (p - 1) + 1)`
    simp only [mem_Ico]
    rw [mem_range] at hk
    omega
  · rw [natCast_two_pow_sub_one]
    have : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
      rw [show 2 * (p - 1) = (p - 1) * 2 by ring, two_pow_mul_p_sub_one hp2]
    rw [this, sub_self]

lemma a_mod_two (n : ℕ) (hn : 1 ≤ n) : a n % 2 = 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [a_one]
  | succ n hn ih =>
    rw [a_succ, Nat.add_mod, Nat.mul_mod, ih]
    have hodd : (2 ^ n - 1) % 2 = 1 := by
      have hle : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have heven : 2 ^ n % 2 = 0 := by
        rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega : n ≠ 0), Nat.zero_mod]
      omega
    have hevenPow : 2 ^ Nat.choose (n + 1) 2 % 2 = 0 := by
      have hpos : 1 ≤ Nat.choose (n + 1) 2 := by
        rw [choose_two_succ]
        omega
      rw [Nat.pow_mod, Nat.mod_self,
        zero_pow (by omega : Nat.choose (n + 1) 2 ≠ 0), Nat.zero_mod]
    rw [hodd, hevenPow]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  by_cases hp2 : p = 2
  · subst hp2
    rw [a_mod_two n hn, a_mod_two (n + 2 * (2 - 1)) (by omega)]
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.natCast_eq_natCast_iff']
    -- It suffices to prove the equality in `ZMod p`, by induction on `n`.
    revert hn
    apply Nat.le_induction
    · -- base: `a(1 + 2(p-1)) ≡ a(1) ≡ 1`
      have hppos : 1 ≤ p := hp.one_le
      have hEq : 1 + 2 * (p - 1) = 2 * p - 1 := by omega
      rw [hEq, a_two_mul_p_sub_one hp2, a_one, Nat.cast_one]
    · intro n hn ih
      rw [show n + 1 + 2 * (p - 1) = n + 2 * (p - 1) + 1 by ring]
      rw [a_succ_cast, a_succ_cast, ih]
      have hpow : (2 : ZMod p) ^ (n + 2 * (p - 1)) = (2 : ZMod p) ^ n := by
        rw [pow_add, show 2 * (p - 1) = (p - 1) * 2 by ring, two_pow_mul_p_sub_one hp2, mul_one]
      have hch : (2 : ZMod p) ^ Nat.choose (n + 2 * (p - 1) + 1) 2 =
          (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
        rw [show n + 2 * (p - 1) + 1 = n + 1 + 2 * (p - 1) by ring]
        exact two_pow_choose_period hp2 (n + 1)
      rw [hpow, hch]
