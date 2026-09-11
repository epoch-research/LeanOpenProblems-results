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

lemma a_succ (n : ℕ) : a (n + 1) = (2 ^ n - 1) * a n + 2 ^ Nat.choose (n + 1) 2 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [Finset.prod_Ico_succ_top (by omega)]
  ring

lemma cast_a_succ (p : ℕ) (n : ℕ) :
    ((a (n+1) : ℕ) : ZMod p) = ((2 : ZMod p) ^ n - 1) * (a n : ZMod p) + 2 ^ Nat.choose (n+1) 2 := by
  rw [a_succ]
  push_cast [Nat.cast_sub Nat.one_le_two_pow]
  ring

lemma two_mul_choose_succ_two (k : ℕ) : 2 * Nat.choose (k+1) 2 = (k+1) * k := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel' (by rw [mul_comm]; exact (Nat.even_mul_succ_self k).two_dvd)

lemma pow_periodic (p : ℕ) [Fact p.Prime] (x : ZMod p) (j K : ℕ) (hj : 1 ≤ j) :
    x ^ (j + (p-1) * K) = x ^ j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, ← add_assoc, pow_add, ih, ← pow_add]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j-1, by omega⟩
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
    rw [show j' + 1 + (p - 1) = j' + p by omega, pow_add, ZMod.pow_card, ← pow_succ]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  haveI := Fact.mk hp
  intro n hn
  rw [← ZMod.natCast_eq_natCast_iff']
  induction n, hn using Nat.le_induction with
  | base =>
    rcases hp.eq_two_or_odd' with rfl | hodd
    · decide
    · have h2 : (2 : ZMod p) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at h'
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'
        subst this
        exact absurd hodd (by decide)
      have hpow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
      obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
      have hq' : p - 1 = q := by omega
      rw [show 1 + 2 * (p - 1) = 2 * (p-1) + 1 by omega, cast_a_succ, pow_mul', hpow]
      have hc : Nat.choose (2 * (p - 1) + 1) 2 = (p - 1) * (2 * (p-1) + 1) := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        rw [two_mul_choose_succ_two]; ring
      rw [hc, pow_mul, hpow]
      simp [a]
  | succ n hn ih =>
    rw [show n + 1 + 2*(p-1) = (n + 2*(p-1)) + 1 by omega, cast_a_succ, cast_a_succ, ih]
    congr 1
    · congr 2
      rw [mul_comm]
      exact pow_periodic p 2 n 2 hn
    · have hc : Nat.choose (n + 2*(p-1) + 1) 2 = Nat.choose (n+1) 2 + (p-1) * (2*n + 2*(p-1) + 1) := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        rw [mul_add, two_mul_choose_succ_two, two_mul_choose_succ_two]; ring
      rw [hc, pow_periodic]
      have : 0 < Nat.choose (n+1) 2 := Nat.choose_pos (by omega)
      omega

theorem oeis_340881_conjecture_0.disproof : ¬ (type_of% @oeis_340881_conjecture_0) := sorry
