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

/-- Recurrence for the sequence: `a (n+1) = (2^n - 1) * a n + 2^(C(n+1,2))`. -/
lemma a_succ (n : ℕ) :
    a (n + 1) = (2 ^ n - 1) * a n + 2 ^ (Nat.choose (n + 1) 2) := by
  simp only [a]
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt hk)]
  ring

/-- `choose (k+1) 2 * 2 = (k+1) * k`. -/
lemma two_mul_choose (k : ℕ) : Nat.choose (k + 1) 2 * 2 = (k + 1) * k := by
  have hdvd : 2 ∣ (k + 1) * k := by
    rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self k).two_dvd
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.div_mul_cancel hdvd]

/-- Periodicity of the triangular-number exponent modulo a shift of `2*q`. -/
lemma choose_period_identity (m q : ℕ) :
    Nat.choose (m + 2 * q + 1) 2 = Nat.choose (m + 1) 2 + q * (2 * m + 2 * q + 1) := by
  have h1 := two_mul_choose (m + 2 * q)
  have h2 := two_mul_choose m
  have key2 : Nat.choose (m + 2 * q + 1) 2 * 2
      = (Nat.choose (m + 1) 2 + q * (2 * m + 2 * q + 1)) * 2 := by
    rw [Nat.add_mul, h2, h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) key2

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- The recurrence cast into `ZMod p`.
  have hrec : ∀ m : ℕ,
      ((a (m + 1) : ZMod p))
        = ((2 : ZMod p) ^ m - 1) * (a m : ZMod p) + (2 : ZMod p) ^ (Nat.choose (m + 1) 2) := by
    intro m
    have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    rw [a_succ]
    push_cast [Nat.cast_sub h1]
    ring
  -- The main congruence, proved in `ZMod p`.
  have key : ∀ n : ℕ, n ≥ 1 → (a (n + 2 * (p - 1)) : ZMod p) = (a n : ZMod p) := by
    by_cases hp2 : p = 2
    · -- Case `p = 2`: the sequence is eventually constant mod 2.
      subst hp2
      have c2 : ∀ m : ℕ, m ≥ 1 → ((a (m + 1) : ZMod 2)) = (a m : ZMod 2) := by
        intro m hm
        rw [hrec m]
        have h2 : (2 : ZMod 2) = 0 := by simpa using ZMod.natCast_self 2
        have hpow1 : (2 : ZMod 2) ^ m = 0 := by rw [h2, zero_pow (by omega : m ≠ 0)]
        have hc : Nat.choose (m + 1) 2 ≠ 0 := by
          have := Nat.choose_pos (show 2 ≤ m + 1 by omega)
          omega
        have hpow2 : (2 : ZMod 2) ^ (Nat.choose (m + 1) 2) = 0 := by rw [h2, zero_pow hc]
        rw [hpow1, hpow2]
        linear_combination (-(a m : ZMod 2)) * h2
      intro n hn
      have e : n + 2 * (2 - 1) = (n + 1) + 1 := by norm_num
      rw [e]
      calc (a ((n + 1) + 1) : ZMod 2) = (a (n + 1) : ZMod 2) := c2 (n + 1) (by omega)
        _ = (a n : ZMod 2) := c2 n hn
    · -- Case `p` odd prime: use Fermat's little theorem.
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro hzero
        have hz : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hzero
        rw [ZMod.natCast_eq_zero_iff] at hz
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hz)
      have hfermat : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
      have hP : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
        rw [show 2 * (p - 1) = (p - 1) * 2 from by ring, pow_mul, hfermat, one_pow]
      have cper : ∀ m, (2 : ZMod p) ^ (m + 2 * (p - 1)) = (2 : ZMod p) ^ m := by
        intro m; rw [pow_add, hP, mul_one]
      have dper : ∀ m, (2 : ZMod p) ^ (Nat.choose (m + 2 * (p - 1) + 1) 2)
          = (2 : ZMod p) ^ (Nat.choose (m + 1) 2) := by
        intro m
        rw [choose_period_identity m (p - 1), pow_add, pow_mul, hfermat, one_pow, mul_one]
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        have e0 : (1 : ℕ) + 2 * (p - 1) = (0 + 2 * (p - 1)) + 1 := by ring
        have e1 : (1 : ℕ) = 0 + 1 := by ring
        rw [e0, hrec (0 + 2 * (p - 1)), cper 0, dper 0]
        conv_rhs => rw [e1, hrec 0]
        ring
      | succ m hm ih =>
        have e : m + 1 + 2 * (p - 1) = (m + 2 * (p - 1)) + 1 := by ring
        rw [e, hrec (m + 2 * (p - 1)), cper m, dper m, ih]
        exact (hrec m).symm
  intro n hn
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (key n hn)
