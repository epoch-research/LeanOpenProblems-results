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

lemma a_step (n : ℕ) :
    a (n + 1) = a n * (2 ^ n - 1) + 2 ^ Nat.choose (n + 1) 2 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_Ico_succ_top (by have := Finset.mem_range.mp hk; omega)]
    ring
  · simp

lemma a_step_cast (p n : ℕ) :
    (a (n + 1) : ZMod p) = (a n : ZMod p) * ((2 : ZMod p) ^ n - 1) +
      (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
  rw [a_step]
  push_cast [Nat.one_le_pow n 2 (by omega)]
  rfl

lemma two_choose (n : ℕ) : Nat.choose (n + 1 + 1) 2 =
    (n + 1) + Nat.choose (n + 1) 2 := by
  simpa using Nat.choose_succ_succ (n + 1) 1

lemma shifted_power (p d : ℕ) (h : (2 : ZMod p) ^ d = 1) :
    ∀ n : ℕ, (2 : ZMod p) ^ Nat.choose (n + 2 * d + 1) 2 =
      (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
  have hL : (2 : ZMod p) ^ (2 * d) = 1 := by
    rw [mul_comm 2 d, pow_mul, h, one_pow]
  intro n
  induction n with
  | zero =>
    have hc : Nat.choose (2 * d + 1) 2 = (2 * d + 1) * d := by
      rw [Nat.choose_two_right]
      simp only [Nat.add_sub_cancel]
      rw [show (2 * d + 1) * (2 * d) = ((2 * d + 1) * d) * 2 by ring,
        Nat.mul_div_cancel _ (by omega)]
    simp only [zero_add, hc, Nat.choose_eq_zero_of_lt (by omega : 1 < 2), pow_zero]
    rw [mul_comm, pow_mul, h, one_pow]
  | succ n ih =>
    rw [show n + 1 + 2 * d + 1 = (n + 2 * d) + 1 + 1 by omega,
      two_choose, two_choose, pow_add _ (n + 2 * d + 1), ih,
      show n + 2 * d + 1 = (n + 1) + 2 * d by omega, pow_add, hL, mul_one,
      pow_add]
    simp only [pow_add]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
  by_cases hp2 : p = 2
  · subst p
    have ha : ∀ m : ℕ, (a (m + 1) : ZMod 2) = 1 := by
      intro m
      induction m with
      | zero => norm_num [a]
      | succ m ih =>
        rw [a_step_cast, ih]
        have hpos : 0 < Nat.choose (m + 1 + 1) 2 := Nat.choose_pos (by omega)
        rw [show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : m + 1 ≠ 0),
          zero_pow (by omega : Nat.choose (m + 1 + 1) 2 ≠ 0)]
        decide
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using (ha (k + 2)).trans (ha k).symm
  · haveI : Fact p.Prime := ⟨hp⟩
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
      have := Nat.le_of_dvd (by omega : 0 < 2) hd
      have := hp.two_le
      omega
    have hF : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one htwo
    have hL : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
      rw [mul_comm 2, pow_mul, hF, one_pow]
    have hpow (m : ℕ) : (2 : ZMod p) ^ (m + 2 * (p - 1)) = (2 : ZMod p) ^ m := by
      rw [pow_add, hL, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    clear hn
    induction k with
    | zero =>
      rw [show Nat.succ 0 + 2 * (p - 1) = 2 * (p - 1) + 1 by omega, a_step_cast, hL]
      have hc := shifted_power p (p - 1) hF 0
      simp only [zero_add] at hc
      rw [hc]
      norm_num [a]
    | succ k ih =>
      rw [show (k + 1).succ + 2 * (p - 1) = (k.succ + 2 * (p - 1)) + 1 by omega,
        a_step_cast, a_step_cast, ih, hpow, shifted_power p (p - 1) hF]


theorem oeis_340881_conjecture_0.disproof : ¬ (type_of% @oeis_340881_conjecture_0) := sorry
