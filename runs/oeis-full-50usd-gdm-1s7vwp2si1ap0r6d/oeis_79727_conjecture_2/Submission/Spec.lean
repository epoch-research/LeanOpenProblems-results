import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/--
A079727: $a(n) = 1 + \binom{2}{1}^3 + \binom{4}{2}^3 + \cdots + \binom{2n}{n}^3$.
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^3$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k : ℕ => (Nat.choose (2 * k) k) ^ 3)

/--
A003625: Primes $p$ such that $p \equiv 3, 5, 7, \text{ or } 13 \pmod{14}$.
This set of primes is relevant to the conjectures on A079727.
-/
def IsInA003625 (p : ℕ) : Prop :=
  Nat.Prime p ∧ (p % 14 = 3 ∨ p % 14 = 5 ∨ p % 14 = 7 ∨ p % 14 = 13)

def choose_fast (n k : ℕ) : ℕ :=
  if k ≤ n then
    n.factorial / (k.factorial * (n - k).factorial)
  else
    0

theorem choose_fast_eq_choose (n k : ℕ) : choose_fast n k = n.choose k := by
  unfold choose_fast
  split_ifs with hk
  · rw [← Nat.choose_eq_factorial_div_factorial hk]
  · rw [Nat.choose_eq_zero_of_lt]
    omega

def sum_dc_fuel (fuel : ℕ) (f : ℕ → ℕ) (start : ℕ) (len : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if len = 0 then
      0
    else if len = 1 then
      f start
    else
      sum_dc_fuel fuel' f start (len / 2) + sum_dc_fuel fuel' f (start + len / 2) (len - len / 2)

theorem sum_dc_fuel_eq (fuel : ℕ) (f : ℕ → ℕ) (start len : ℕ) (h_fuel : len ≤ fuel) :
    sum_dc_fuel fuel f start len = (Finset.range len).sum (fun i => f (start + i)) := by
  induction fuel generalizing start len with
  | zero =>
    have h_len : len = 0 := by omega
    subst h_len
    rfl
  | succ fuel' ih =>
    by_cases h_len0 : len = 0
    · subst h_len0
      rfl
    by_cases h_len1 : len = 1
    · subst h_len1
      simp [sum_dc_fuel]
    -- Now len ≥ 2
    have h_len_ge : len ≥ 2 := by omega
    simp only [sum_dc_fuel, h_len0, h_len1, ↓reduceIte]
    have h1 : len / 2 ≤ fuel' := by omega
    have h2 : len - len / 2 ≤ fuel' := by omega
    rw [ih start (len / 2) h1]
    rw [ih (start + len / 2) (len - len / 2) h2]
    -- Now we want to show that sum over range (len / 2) and range (len - len / 2) is sum over range len
    have h_split : len = len / 2 + (len - len / 2) := by omega
    conv_rhs =>
      rw [h_split]
      rw [Finset.sum_range_add]
    congr 2
    ext x
    congr 1
    omega

def a_dc (n : ℕ) : ℕ :=
  sum_dc_fuel (n + 1) (fun k : ℕ => (choose_fast (2 * k) k) ^ 3) 0 (n + 1)

theorem a_dc_eq_a (n : ℕ) : a_dc n = a n := by
  unfold a_dc a
  rw [sum_dc_fuel_eq (n + 1) (fun k => (choose_fast (2 * k) k) ^ 3) 0 (n + 1) (by omega)]
  congr 1
  ext k
  simp only [zero_add]
  rw [choose_fast_eq_choose]

lemma prime_cases {p : ℕ} (h : IsInA003625 p) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 31 ∨ p = 41 ∨ p = 47 ∨ p = 59 ∨ p = 61 ∨ p = 73 ∨ p = 83 ∨ p = 89 ∨ p = 97 ∨ p ≥ 101 := by
  have hp_prime := h.1
  have hp_or := h.2
  have h_or : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 23 ∨ p = 24 ∨ p = 25 ∨ p = 26 ∨ p = 27 ∨ p = 28 ∨ p = 29 ∨ p = 30 ∨ p = 31 ∨ p = 32 ∨ p = 33 ∨ p = 34 ∨ p = 35 ∨ p = 36 ∨ p = 37 ∨ p = 38 ∨ p = 39 ∨ p = 40 ∨ p = 41 ∨ p = 42 ∨ p = 43 ∨ p = 44 ∨ p = 45 ∨ p = 46 ∨ p = 47 ∨ p = 48 ∨ p = 49 ∨ p = 50 ∨ p = 51 ∨ p = 52 ∨ p = 53 ∨ p = 54 ∨ p = 55 ∨ p = 56 ∨ p = 57 ∨ p = 58 ∨ p = 59 ∨ p = 60 ∨ p = 61 ∨ p = 62 ∨ p = 63 ∨ p = 64 ∨ p = 65 ∨ p = 66 ∨ p = 67 ∨ p = 68 ∨ p = 69 ∨ p = 70 ∨ p = 71 ∨ p = 72 ∨ p = 73 ∨ p = 74 ∨ p = 75 ∨ p = 76 ∨ p = 77 ∨ p = 78 ∨ p = 79 ∨ p = 80 ∨ p = 81 ∨ p = 82 ∨ p = 83 ∨ p = 84 ∨ p = 85 ∨ p = 86 ∨ p = 87 ∨ p = 88 ∨ p = 89 ∨ p = 90 ∨ p = 91 ∨ p = 92 ∨ p = 93 ∨ p = 94 ∨ p = 95 ∨ p = 96 ∨ p = 97 ∨ p = 98 ∨ p = 99 ∨ p = 100 ∨ p ≥ 101 := by omega
  rcases h_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_ge
  · revert hp_prime; decide -- p = 0
  · revert hp_prime; decide -- p = 1
  · revert hp_or; decide -- p = 2
  · left; rfl -- p = 3
  · revert hp_prime; decide -- p = 4
  · right; left; rfl -- p = 5
  · revert hp_prime; decide -- p = 6
  · right; right; left; rfl -- p = 7
  · revert hp_prime; decide -- p = 8
  · revert hp_prime; decide -- p = 9
  · revert hp_prime; decide -- p = 10
  · revert hp_or; decide -- p = 11
  · revert hp_prime; decide -- p = 12
  · right; right; right; left; rfl -- p = 13
  · revert hp_prime; decide -- p = 14
  · revert hp_prime; decide -- p = 15
  · revert hp_prime; decide -- p = 16
  · right; right; right; right; left; rfl -- p = 17
  · revert hp_prime; decide -- p = 18
  · right; right; right; right; right; left; rfl -- p = 19
  · revert hp_prime; decide -- p = 20
  · revert hp_prime; decide -- p = 21
  · revert hp_prime; decide -- p = 22
  · revert hp_or; decide -- p = 23
  · revert hp_prime; decide -- p = 24
  · revert hp_prime; decide -- p = 25
  · revert hp_prime; decide -- p = 26
  · revert hp_prime; decide -- p = 27
  · revert hp_prime; decide -- p = 28
  · revert hp_or; decide -- p = 29
  · revert hp_prime; decide -- p = 30
  · right; right; right; right; right; right; left; rfl -- p = 31
  · revert hp_prime; decide -- p = 32
  · revert hp_prime; decide -- p = 33
  · revert hp_prime; decide -- p = 34
  · revert hp_prime; decide -- p = 35
  · revert hp_prime; decide -- p = 36
  · revert hp_or; decide -- p = 37
  · revert hp_prime; decide -- p = 38
  · revert hp_prime; decide -- p = 39
  · revert hp_prime; decide -- p = 40
  · right; right; right; right; right; right; right; left; rfl -- p = 41
  · revert hp_prime; decide -- p = 42
  · revert hp_or; decide -- p = 43
  · revert hp_prime; decide -- p = 44
  · revert hp_prime; decide -- p = 45
  · revert hp_prime; decide -- p = 46
  · right; right; right; right; right; right; right; right; left; rfl -- p = 47
  · revert hp_prime; decide -- p = 48
  · revert hp_prime; decide -- p = 49
  · revert hp_prime; decide -- p = 50
  · revert hp_prime; decide -- p = 51
  · revert hp_prime; decide -- p = 52
  · revert hp_or; decide -- p = 53
  · revert hp_prime; decide -- p = 54
  · revert hp_prime; decide -- p = 55
  · revert hp_prime; decide -- p = 56
  · revert hp_prime; decide -- p = 57
  · revert hp_prime; decide -- p = 58
  · right; right; right; right; right; right; right; right; right; left; rfl -- p = 59
  · revert hp_prime; decide -- p = 60
  · right; right; right; right; right; right; right; right; right; right; left; rfl -- p = 61
  · revert hp_prime; decide -- p = 62
  · revert hp_prime; decide -- p = 63
  · revert hp_prime; decide -- p = 64
  · revert hp_prime; decide -- p = 65
  · revert hp_prime; decide -- p = 66
  · revert hp_or; decide -- p = 67
  · revert hp_prime; decide -- p = 68
  · revert hp_prime; decide -- p = 69
  · revert hp_prime; decide -- p = 70
  · revert hp_or; decide -- p = 71
  · revert hp_prime; decide -- p = 72
  · right; right; right; right; right; right; right; right; right; right; right; left; rfl -- p = 73
  · revert hp_prime; decide -- p = 74
  · revert hp_prime; decide -- p = 75
  · revert hp_prime; decide -- p = 76
  · revert hp_prime; decide -- p = 77
  · revert hp_prime; decide -- p = 78
  · revert hp_or; decide -- p = 79
  · revert hp_prime; decide -- p = 80
  · revert hp_prime; decide -- p = 81
  · revert hp_prime; decide -- p = 82
  · right; right; right; right; right; right; right; right; right; right; right; right; left; rfl -- p = 83
  · revert hp_prime; decide -- p = 84
  · revert hp_prime; decide -- p = 85
  · revert hp_prime; decide -- p = 86
  · revert hp_prime; decide -- p = 87
  · revert hp_prime; decide -- p = 88
  · right; right; right; right; right; right; right; right; right; right; right; right; right; left; rfl -- p = 89
  · revert hp_prime; decide -- p = 90
  · revert hp_prime; decide -- p = 91
  · revert hp_prime; decide -- p = 92
  · revert hp_prime; decide -- p = 93
  · revert hp_prime; decide -- p = 94
  · revert hp_prime; decide -- p = 95
  · revert hp_prime; decide -- p = 96
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rfl -- p = 97
  · revert hp_prime; decide -- p = 98
  · revert hp_prime; decide -- p = 99
  · revert hp_prime; decide -- p = 100
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; exact h_ge

/--
Conjecture 2 from A079727 (Peter Bala's Conjectures):
If prime p is in A003625 then a(p*(p-1)) == p^2 (mod p^3).
-/
theorem oeis_79727_conjecture_2 {p : ℕ} (h_prime_in_A003625 : IsInA003625 p) :
  a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  have h_cases := prime_cases h_prime_in_A003625
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_ge
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · rw [← a_dc_eq_a]; decide
  · have h_or := h_prime_in_A003625.2
    rcases h_or with hp3 | hp5 | hp7 | hp13
    · sorry
    · sorry
    · have h_div : 7 ∣ p := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have h1 : p % 7 = (p % 14) % 7 := by omega
        rw [hp7] at h1
        exact h1
      have hp_eq_7 : p = 7 := by
        have h_prime := h_prime_in_A003625.1
        have h_or' := Nat.Prime.eq_one_or_self_of_dvd h_prime 7 h_div
        rcases h_or' with h_one | h_self
        · contradiction
        · exact h_self.symm
      omega
    · sorry

