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

/-- Recurrence for the sequence `a`: `a (n+1) = (2^n - 1) * a n + 2 ^ C(n+1, 2)`. -/
theorem a_succ (n : ℕ) :
    a (n + 1) = (2 ^ n - 1) * a n + 2 ^ Nat.choose (n + 1) 2 := by
  unfold a
  rw [Finset.sum_range_succ]
  have hlast : (2 ^ Nat.choose (n + 1) 2) *
      (Finset.prod (Finset.Ico (n + 1) (n + 1)) fun j ↦ (2 ^ j - 1))
      = 2 ^ Nat.choose (n + 1) 2 := by
    rw [Finset.Ico_self, Finset.prod_empty, mul_one]
  rw [hlast]
  have hsum : (Finset.sum (Finset.range n) fun k ↦
      (2 ^ Nat.choose (k + 1) 2) *
      (Finset.prod (Finset.Ico (k + 1) (n + 1)) fun j ↦ (2 ^ j - 1)))
      = (2 ^ n - 1) * (Finset.sum (Finset.range n) fun k ↦
      (2 ^ Nat.choose (k + 1) 2) *
      (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.prod_Ico_succ_top (by omega : k + 1 ≤ n)]
    ring
  rw [hsum]

/-- `a 1 = 1`. -/
theorem a_one : a 1 = 1 := by
  simp [a]

/-- The recurrence cast into `ZMod p`. -/
theorem a_succ_zmod (p : ℕ) (n : ℕ) :
    ((a (n + 1) : ZMod p)) =
      ((2 : ZMod p) ^ n - 1) * (a n : ZMod p) + (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  rw [a_succ]
  push_cast [Nat.cast_sub h1]
  ring

/-- The `p = 2` case: `a n` is odd for `n ≥ 1`, hence periodic mod 2. -/
theorem oeis_340881_two :
    ∀ n, 1 ≤ n → (a (n + 2 * (2 - 1)) : ZMod 2) = (a n : ZMod 2) := by
  have key : ∀ n, 1 ≤ n → (a n : ZMod 2) = 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [a_one]; norm_num
    | succ n hn ih =>
      have e1 : (2 : ZMod 2) ^ n = 0 := by
        rw [show (2 : ZMod 2) = 0 from by decide]; exact zero_pow (by omega)
      have e2 : (2 : ZMod 2) ^ (Nat.choose (n + 1) 2) = 0 := by
        rw [show (2 : ZMod 2) = 0 from by decide]
        exact zero_pow (Nat.choose_pos (by omega)).ne'
      rw [a_succ_zmod, e1, e2, ih]
      decide
  intro n hn
  rw [key _ (by omega), key _ hn]

/-- The odd prime case (`p ≠ 2`): periodicity mod `p` with period `2*(p-1)`. -/
theorem oeis_340881_odd (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ∀ n, 1 ≤ n → (a (n + 2 * (p - 1)) : ZMod p) = (a n : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h0 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h0
    rcases Nat.prime_two.eq_one_or_self_of_dvd p h0 with h1 | h1 <;>
      (have := hp.two_le; omega)
  set c := p - 1 with hc
  have hferm : (2 : ZMod p) ^ c = 1 := by
    have := ZMod.pow_card_sub_one_eq_one h2ne
    rwa [← hc] at this
  have hpow : ∀ k : ℕ, (2 : ZMod p) ^ (c * k) = 1 := by
    intro k; rw [pow_mul, hferm, one_pow]
  have h2c : (2 : ZMod p) ^ (2 * c) = 1 := by rw [mul_comm]; exact hpow 2
  have hchoose2 : ∀ m : ℕ, 2 * Nat.choose m 2 = m * (m - 1) := by
    intro m
    rw [Nat.choose_two_right]
    have hdvd : 2 ∣ m * (m - 1) := by
      rcases Nat.even_or_odd m with he | ho
      · exact he.two_dvd.mul_right _
      · obtain ⟨t, rfl⟩ := ho
        exact ⟨(2 * t + 1) * t, by rw [Nat.add_sub_cancel]; ring⟩
    exact Nat.mul_div_cancel' hdvd
  have hex_base : Nat.choose (2 * c + 1) 2 = c * (2 * c + 1) := by
    have key : 2 * Nat.choose (2 * c + 1) 2 = 2 * (c * (2 * c + 1)) := by
      rw [hchoose2]; simp only [Nat.add_sub_cancel]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) key
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show (1 : ℕ) + 2 * c = 2 * c + 1 from by ring, a_succ_zmod, h2c, sub_self,
      zero_mul, zero_add, hex_base, hpow, a_one]
    norm_num
  | succ n hn ih =>
    have hex_step : Nat.choose (n + 2 * c + 1) 2
        = Nat.choose (n + 1) 2 + c * (2 * n + 2 * c + 1) := by
      have key : 2 * Nat.choose (n + 2 * c + 1) 2
          = 2 * (Nat.choose (n + 1) 2 + c * (2 * n + 2 * c + 1)) := by
        rw [hchoose2, Nat.mul_add, hchoose2]
        simp only [Nat.add_sub_cancel]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) key
    rw [show n + 1 + 2 * c = (n + 2 * c) + 1 from by ring, a_succ_zmod,
      pow_add, h2c, mul_one, ih, hex_step, pow_add, hpow, mul_one, a_succ_zmod]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  rw [← ZMod.natCast_eq_natCast_iff']
  rcases eq_or_ne p 2 with rfl | hp2
  · exact oeis_340881_two n hn
  · exact oeis_340881_odd p hp hp2 n hn
