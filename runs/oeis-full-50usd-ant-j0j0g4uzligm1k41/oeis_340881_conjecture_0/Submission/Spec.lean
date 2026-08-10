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

/-- Recurrence for the sequence: `a (n+1) = (2^n - 1) * a n + 2^C(n+1,2)`. -/
theorem a_succ (n : ℕ) :
    a (n + 1) = (2 ^ n - 1) * a n + 2 ^ (Nat.choose (n + 1) 2) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one,
      Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k + 1 ≤ n := hk
  rw [Finset.prod_Ico_succ_top hkn]
  ring

/-- Additive identity for the second binomial coefficient. -/
theorem choose2_add (q t : ℕ) :
    Nat.choose (q + t) 2 = Nat.choose q 2 + t * q + Nat.choose t 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 : q + (t + 1) = (q + t) + 1 := by ring
      rw [h1, Nat.choose_succ_succ, Nat.choose_one_right, ih,
          Nat.choose_succ_succ, Nat.choose_one_right]
      ring

section prime
variable {p : ℕ} [Fact p.Prime]

/-- The recurrence, cast into `ZMod p`. -/
theorem x_succ (n : ℕ) :
    ((a (n + 1) : ℕ) : ZMod p)
      = (2 ^ n - 1) * ((a n : ℕ) : ZMod p) + 2 ^ (Nat.choose (n + 1) 2) := by
  rw [a_succ n]
  push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
  ring

/-- `2 ^ (2*(p-1)) = 1` in `ZMod p`, from Fermat. -/
theorem two_pow_T (h2 : (2 : ZMod p) ^ (p - 1) = 1) :
    (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
  rw [show 2 * (p - 1) = (p - 1) * 2 by ring, pow_mul, h2, one_pow]

/-- The value `2 ^ C(n, 2)` is invariant under shifting `n` by `2*(p-1)`. -/
theorem two_choose_shift (h2 : (2 : ZMod p) ^ (p - 1) = 1) (q : ℕ) :
    (2 : ZMod p) ^ (Nat.choose (q + 2 * (p - 1)) 2) = 2 ^ (Nat.choose q 2) := by
  rw [choose2_add q (2 * (p - 1)), pow_add, pow_add]
  have hTq : (2 : ZMod p) ^ ((2 * (p - 1)) * q) = 1 := by
    rw [show (2 * (p - 1)) * q = (p - 1) * (2 * q) by ring, pow_mul, h2, one_pow]
  have hcT : (2 : ZMod p) ^ (Nat.choose (2 * (p - 1)) 2) = 1 := by
    have hc : Nat.choose (2 * (p - 1)) 2 = (p - 1) * (2 * (p - 1) - 1) := by
      rw [Nat.choose_two_right,
          show 2 * (p - 1) * (2 * (p - 1) - 1) = 2 * ((p - 1) * (2 * (p - 1) - 1)) by ring,
          Nat.mul_div_cancel_left]
      omega
    rw [hc, pow_mul, h2, one_pow]
  rw [hTq, hcT, mul_one, mul_one]

/-- "Reset" case: when `2^n = 1` in `ZMod p`, the value at `n+1` is forced. -/
theorem caseA (h2 : (2 : ZMod p) ^ (p - 1) = 1) (n : ℕ) (hn : (2 : ZMod p) ^ n = 1) :
    ((a (n + 1 + 2 * (p - 1)) : ℕ) : ZMod p) = ((a (n + 1) : ℕ) : ZMod p) := by
  have e : n + 1 + 2 * (p - 1) = (n + 2 * (p - 1)) + 1 := by ring
  rw [e, x_succ (n + 2 * (p - 1)), x_succ n]
  have hcT : (2 : ZMod p) ^ (n + 2 * (p - 1)) = 1 := by
    rw [pow_add, hn, two_pow_T h2, mul_one]
  rw [hn, hcT, sub_self, zero_mul, zero_mul, zero_add, zero_add]
  have e2 : (n + 2 * (p - 1)) + 1 = (n + 1) + 2 * (p - 1) := by ring
  rw [e2, two_choose_shift h2]

/-- Periodicity for odd primes (in `ZMod p`). -/
theorem main_odd (h2 : (2 : ZMod p) ^ (p - 1) = 1) (n : ℕ) :
    ((a (n + 1 + 2 * (p - 1)) : ℕ) : ZMod p) = ((a (n + 1) : ℕ) : ZMod p) := by
  induction n with
  | zero => exact caseA h2 0 (by simp)
  | succ m ih =>
      by_cases h : (2 : ZMod p) ^ (m + 1) = 1
      · exact caseA h2 (m + 1) h
      · have e : (m + 1) + 1 + 2 * (p - 1) = ((m + 1) + 2 * (p - 1)) + 1 := by ring
        rw [e, x_succ ((m + 1) + 2 * (p - 1)), x_succ (m + 1)]
        have hcoef : (2 : ZMod p) ^ ((m + 1) + 2 * (p - 1)) = 2 ^ (m + 1) := by
          rw [pow_add, two_pow_T h2, mul_one]
        rw [hcoef, (ih : ((a (m + 1 + 2 * (p - 1)) : ℕ) : ZMod p) = _)]
        have e2 : ((m + 1) + 2 * (p - 1)) + 1 = ((m + 1) + 1) + 2 * (p - 1) := by ring
        rw [e2, two_choose_shift h2]

end prime

theorem c1_zmod2 : (0 : ZMod 2) - 1 = 1 := by decide

/-- The `p = 2` step: consecutive terms (index ≥ 1) are equal mod 2. -/
theorem step2 (m : ℕ) : ((a (m + 2) : ℕ) : ZMod 2) = ((a (m + 1) : ℕ) : ZMod 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show m + 2 = (m + 1) + 1 from rfl, x_succ (p := 2) (m + 1)]
  have h1 : (2 : ZMod 2) ^ (m + 1) = 0 := by
    rw [show (2 : ZMod 2) = 0 from rfl]; exact zero_pow (Nat.succ_ne_zero m)
  have c1 : (0 : ZMod 2) - 1 = 1 := c1_zmod2
  have h2c : (2 : ZMod 2) ^ (Nat.choose ((m + 1) + 1) 2) = 0 := by
    rw [show (2 : ZMod 2) = 0 from rfl]
    apply zero_pow
    have : 0 < Nat.choose ((m + 1) + 1) 2 := Nat.choose_pos (by omega)
    omega
  rw [h1, c1, h2c, one_mul, add_zero]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hp2 : p = 2
  · subst hp2
    rw [← ZMod.natCast_eq_natCast_iff']
    show ((a ((m + 1) + 2) : ℕ) : ZMod 2) = ((a (m + 1) : ℕ) : ZMod 2)
    exact (step2 (m + 1)).trans (step2 m)
  · have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
      rw [ZMod.natCast_eq_zero_iff] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have h2 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
    rw [← ZMod.natCast_eq_natCast_iff']
    exact main_odd h2 m
