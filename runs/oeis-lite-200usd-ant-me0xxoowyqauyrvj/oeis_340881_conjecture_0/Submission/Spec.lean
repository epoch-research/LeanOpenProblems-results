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

-- Recurrence for `a`.
private theorem a_succ : ∀ n, a (n+1) = (2^n - 1) * a n + 2 ^ Nat.choose (n+1) 2 := by
  intro n
  simp only [a, Finset.sum_range_succ]
  rw [Finset.Ico_self, Finset.prod_empty, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [Finset.prod_Ico_succ_top (by omega : k + 1 ≤ n)]
  ring

-- `2 * C(m+1, 2) = m * (m+1)`.
private theorem two_mul_choose : ∀ m, 2 * Nat.choose (m+1) 2 = m * (m+1) := by
  intro m
  induction m with
  | zero => decide
  | succ k ih =>
    have hc : Nat.choose (k+1+1) 2 = (k+1) + Nat.choose (k+1) 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [hc, Nat.mul_add, ih]
    ring

private theorem a_one : a 1 = 1 := by simp [a]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- cast recurrence to ZMod p
  have hcast : ∀ n, (a (n+1) : ZMod p)
      = ((2:ZMod p)^n - 1) * (a n : ZMod p) + (2:ZMod p)^(Nat.choose (n+1) 2) := by
    intro n
    have h1 : (1:ℕ) ≤ 2^n := Nat.one_le_pow n 2 (by norm_num)
    rw [a_succ n]
    push_cast [Nat.cast_sub h1]
    ring
  rcases eq_or_ne p 2 with hp2 | hp2
  · -- p = 2 case: `a (m+1)` is always odd
    subst hp2
    have hoddP : ∀ m, Odd (a (m+1)) := by
      intro m
      induction m with
      | zero => rw [a_one]; exact odd_one
      | succ k ih =>
        rw [a_succ (k+1)]
        have he1 : Even (2^(k+1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
        have hle : 1 ≤ 2^(k+1) := Nat.one_le_pow _ _ (by norm_num)
        have ho1 : Odd (2^(k+1) - 1) := Nat.Even.sub_odd hle he1 odd_one
        have he2 : Even (2^(Nat.choose (k+1+1) 2)) :=
          Nat.even_pow.mpr ⟨even_two, (Nat.choose_pos (by omega)).ne'⟩
        exact (ho1.mul ih).add_even he2
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
    have e : m + 1 + 2 * (2-1) = m + 1 + 1 + 1 := by ring
    rw [e]
    have h1 := Nat.odd_iff.mp (hoddP (m+1+1))
    have h2 := Nat.odd_iff.mp (hoddP m)
    omega
  · -- odd prime
    have h2ne : (2:ZMod p) ≠ 0 := by
      have hcast2 : ((2:ℕ):ZMod p) = (2:ZMod p) := by norm_cast
      rw [← hcast2, Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    have hfermat : (2:ZMod p)^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
    have hP2 : (2:ZMod p)^(2*(p-1)) = 1 := by
      rw [mul_comm 2 (p-1), pow_mul, hfermat, one_pow]
    have hA : ∀ n, (2:ZMod p)^(n + 2*(p-1)) = (2:ZMod p)^n := by
      intro n; rw [pow_add, hP2, mul_one]
    have hchoose : ∀ n, Nat.choose (n + 2*(p-1) + 1) 2
        = Nat.choose (n+1) 2 + (p-1)*(2*n + 2*(p-1) + 1) := by
      intro n
      have e1 := two_mul_choose (n + 2*(p-1))
      have e2 := two_mul_choose n
      have key1 : 2 * Nat.choose (n + 2*(p-1) + 1) 2
          = n*(n+1) + 2*((p-1)*(2*n + 2*(p-1) + 1)) := by
        rw [e1]; ring
      have key2 : 2 * (Nat.choose (n+1) 2 + (p-1)*(2*n + 2*(p-1) + 1))
          = n*(n+1) + 2*((p-1)*(2*n + 2*(p-1) + 1)) := by
        rw [Nat.mul_add, e2]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) (key1.trans key2.symm)
    have hB : ∀ n, (2:ZMod p)^(Nat.choose (n + 2*(p-1) + 1) 2)
        = (2:ZMod p)^(Nat.choose (n+1) 2) := by
      intro n
      rw [hchoose n, pow_add, pow_mul, hfermat, one_pow, mul_one]
    -- main step induction
    have step : ∀ m, (a (m+1+2*(p-1)) : ZMod p) = (a (m+1) : ZMod p) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        rw [show 1 + 2*(p-1) = 2*(p-1) + 1 from by ring]
        rw [hcast (2*(p-1))]
        have hc0 : (2:ZMod p)^(2*(p-1)) - 1 = 0 := by rw [hP2]; ring
        rw [hc0]
        have hb0 : (2:ZMod p)^(Nat.choose (2*(p-1)+1) 2) = 1 := by
          have h := hB 0
          simp only [Nat.zero_add] at h
          rw [h, show Nat.choose 1 2 = 0 from rfl, pow_zero]
        rw [hb0, a_one]
        ring
      | succ k ih =>
        rw [show k+1+1+2*(p-1) = (k+1+2*(p-1))+1 from by ring]
        rw [hcast (k+1+2*(p-1))]
        rw [show k+1+2*(p-1)+1 = (k+1)+2*(p-1)+1 from by ring]
        rw [hA (k+1), hB (k+1), ih, hcast (k+1)]
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (step m)
