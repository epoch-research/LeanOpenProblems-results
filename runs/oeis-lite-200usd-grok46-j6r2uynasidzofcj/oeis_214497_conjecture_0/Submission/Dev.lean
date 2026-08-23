import FormalConjectures.Util.ProblemImports

open Nat

/-
Structural theory for A214497.
-/

/-- If `k ≥ 3^n` then truncated subtraction yields `0`, and `0` is not prime. -/
lemma not_prime_pair_of_k_ge (n k : ℕ) (h : 3 ^ n ≤ k) :
    ¬ (Nat.Prime ((3 ^ n - k) * 2 ^ n - 1) ∧
       Nat.Prime ((3 ^ n - k) * 2 ^ n + 1)) := by
  intro ⟨hA, _⟩
  have : 3 ^ n - k = 0 := tsub_eq_zero_of_le h
  simp only [this, zero_mul, zero_tsub] at hA
  exact Nat.not_prime_zero hA

lemma k_lt_pow3_of_pair (n k : ℕ)
    (h : Nat.Prime ((3 ^ n - k) * 2 ^ n - 1) ∧
         Nat.Prime ((3 ^ n - k) * 2 ^ n + 1)) : k < 3 ^ n := by
  by_contra hle
  exact not_prime_pair_of_k_ge n k (le_of_not_gt hle) h

/-- Translation between the `k`-form and the `m`-form. -/
lemma exists_k_iff_exists_m (n : ℕ) :
    (∃ k : ℕ, Nat.Prime ((3 ^ n - k) * 2 ^ n - 1) ∧
              Nat.Prime ((3 ^ n - k) * 2 ^ n + 1)) ↔
    (∃ m : ℕ, 0 < m ∧ m ≤ 3 ^ n ∧
              Nat.Prime (m * 2 ^ n - 1) ∧ Nat.Prime (m * 2 ^ n + 1)) := by
  constructor
  · intro ⟨k, hk⟩
    have hlt := k_lt_pow3_of_pair n k hk
    refine ⟨3 ^ n - k, tsub_pos_of_lt hlt, Nat.sub_le _ _, hk⟩
  · intro ⟨m, hmpos, hmle, hA, hB⟩
    refine ⟨3 ^ n - m, ?_⟩
    have : 3 ^ n - (3 ^ n - m) = m := Nat.sub_sub_self hmle
    simpa [this] using And.intro hA hB

/-- If `3 ∤ m` then `3` divides one of the pair. -/
lemma three_divides_one_of_pair (n m : ℕ) (hm : ¬ 3 ∣ m) :
    3 ∣ m * 2 ^ n - 1 ∨ 3 ∣ m * 2 ^ n + 1 := by
  have hm0 : (m : ZMod 3) ≠ 0 := by
    intro h
    exact hm ((ZMod.natCast_eq_zero_iff m 3).mp h)
  have hm' : (m : ZMod 3) = 1 ∨ (m : ZMod 3) = -1 := by
    have hv : (m : ZMod 3).val < 3 := ZMod.val_lt _
    have hv' : (m : ZMod 3).val ≠ 0 := by
      intro h
      apply hm0
      exact (ZMod.val_eq_zero (m : ZMod 3)).mp h
    interval_cases hvq : (m : ZMod 3).val
    · contradiction
    · left
      apply (ZMod.val_injective 3)
      rw [hvq]; rfl
    · right
      apply (ZMod.val_injective 3)
      rw [hvq]; decide
  have h2 : (2 : ZMod 3) = -1 := by decide
  have hprod : (m : ZMod 3) * (2 : ZMod 3) ^ n = 1 ∨
               (m : ZMod 3) * (2 : ZMod 3) ^ n = -1 := by
    rw [h2]
    rcases hm' with h | h <;> rcases Nat.even_or_odd n with he | ho
    · left; simp [h, Even.neg_one_pow he]
    · right; simp [h, Odd.neg_one_pow ho]
    · right; simp [h, Even.neg_one_pow he]
    · left; simp [h, Odd.neg_one_pow ho]
  rcases hprod with h | h
  · left
    have hpos : 1 ≤ m * 2 ^ n := by
      by_cases hm0' : m = 0
      · subst hm0'; exact (hm (by decide)).elim
      · exact one_le_mul (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0')) Nat.one_le_two_pow
    refine (ZMod.natCast_eq_zero_iff (m * 2 ^ n - 1) 3).mp ?_
    rw [Nat.cast_sub hpos, Nat.cast_one, Nat.cast_mul, Nat.cast_pow]
    change (m : ZMod 3) * (2 : ZMod 3) ^ n - 1 = 0
    rw [h]; exact sub_self 1
  · right
    refine (ZMod.natCast_eq_zero_iff (m * 2 ^ n + 1) 3).mp ?_
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow]
    change (m : ZMod 3) * (2 : ZMod 3) ^ n + 1 = 0
    rw [h]; exact neg_add_cancel 1

lemma eight_le_two_pow_of_three_le {n : ℕ} (hn : 3 ≤ n) : 8 ≤ 2 ^ n := by
  calc
    8 = 2 ^ 3 := by decide
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn

/-- For `n ≥ 3` a successful `m` must be divisible by `3`. -/
lemma three_dvd_m_of_pair {n m : ℕ} (hn : 3 ≤ n)
    (hA : Nat.Prime (m * 2 ^ n - 1)) (hB : Nat.Prime (m * 2 ^ n + 1)) :
    3 ∣ m := by
  by_contra hm
  have h8 : 8 ≤ 2 ^ n := eight_le_two_pow_of_three_le hn
  have hmpos : 0 < m := by
    by_contra hmz
    simp at hmz
    subst hmz
    simp at hA
    exact Nat.not_prime_zero hA
  have hge : 8 ≤ m * 2 ^ n :=
    le_trans h8 (Nat.le_mul_of_pos_left (2 ^ n) hmpos)
  rcases three_divides_one_of_pair n m hm with hdvd | hdvd
  · have hAeq : m * 2 ^ n - 1 = 3 :=
      (Nat.Prime.dvd_iff_eq hA (by decide : (3 : ℕ) ≠ 1)).mp hdvd
    omega
  · have hBeq : m * 2 ^ n + 1 = 3 :=
      (Nat.Prime.dvd_iff_eq hB (by decide : (3 : ℕ) ≠ 1)).mp hdvd
    omega

/-- Even `m` at exponent `n` yields `m/2` at exponent `n+1` (same primes). -/
lemma lift_even {n m : ℕ} (hm : Even m)
    (hA : Nat.Prime (m * 2 ^ n - 1)) (hB : Nat.Prime (m * 2 ^ n + 1)) :
    Nat.Prime ((m / 2) * 2 ^ (n + 1) - 1) ∧
    Nat.Prime ((m / 2) * 2 ^ (n + 1) + 1) := by
  obtain ⟨t, ht⟩ := hm
  have hdiv : m / 2 = t := by
    rw [ht]
    have : t + t = 2 * t := by ring
    rw [this, Nat.mul_div_right t (by decide)]
  have hmul : (m / 2) * 2 ^ (n + 1) = m * 2 ^ n := by
    rw [hdiv, ht]
    have : t + t = 2 * t := by ring
    rw [this, pow_succ]
    ring
  constructor <;> rw [hmul]
  · exact hA
  · exact hB

lemma lift_even_le {n m : ℕ} (hmle : m ≤ 3 ^ n) :
    m / 2 ≤ 3 ^ (n + 1) := by
  calc
    m / 2 ≤ m := Nat.div_le_self _ _
    _ ≤ 3 ^ n := hmle
    _ ≤ 3 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ _)

/-- Going down one exponent: `2m` at `n-1` gives the same pair. -/
lemma descend_mul_two {n m : ℕ} (hn : 0 < n)
    (hA : Nat.Prime (m * 2 ^ n - 1)) (hB : Nat.Prime (m * 2 ^ n + 1)) :
    Nat.Prime ((2 * m) * 2 ^ (n - 1) - 1) ∧
    Nat.Prime ((2 * m) * 2 ^ (n - 1) + 1) := by
  have hmul : (2 * m) * 2 ^ (n - 1) = m * 2 ^ n := by
    have hsucc : (n - 1).succ = n := Nat.sub_add_cancel hn
    calc
      2 * m * 2 ^ (n - 1) = m * (2 * 2 ^ (n - 1)) := by ring
      _ = m * 2 ^ (n - 1).succ := by rw [← pow_succ']
      _ = m * 2 ^ n := by rw [hsucc]
  constructor <;> rw [hmul]
  · exact hA
  · exact hB

/-- Size condition for descending one exponent. -/
lemma descend_size {n m : ℕ} (h : 2 * m ≤ 3 ^ (n - 1)) :
    2 * m ≤ 3 ^ (n - 1) := h

/-- Shifting a pair at exponent `N` down to exponent `n ≤ N` uses the same primes. -/
lemma pair_shift {N n m0 : ℕ} (hn : n ≤ N)
    (hA : Nat.Prime (m0 * 2 ^ N - 1)) (hB : Nat.Prime (m0 * 2 ^ N + 1)) :
    Nat.Prime ((m0 * 2 ^ (N - n)) * 2 ^ n - 1) ∧
    Nat.Prime ((m0 * 2 ^ (N - n)) * 2 ^ n + 1) := by
  have hmul : (m0 * 2 ^ (N - n)) * 2 ^ n = m0 * 2 ^ N := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  constructor <;> rw [hmul]
  · exact hA
  · exact hB

/-- Consequently a pair at `N` with odd part `m0` yields a `k` at every
`n ≤ N` satisfying the size bound `m0 * 2^{N-n} ≤ 3^n`. -/
lemma exists_k_of_shift {N n m0 : ℕ} (hn : n ≤ N)
    (hA : Nat.Prime (m0 * 2 ^ N - 1)) (hB : Nat.Prime (m0 * 2 ^ N + 1))
    (hsz : m0 * 2 ^ (N - n) ≤ 3 ^ n) (hm0 : 0 < m0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * 2 ^ n - 1) ∧
             Nat.Prime ((3 ^ n - k) * 2 ^ n + 1) := by
  refine (exists_k_iff_exists_m n).mpr ?_
  refine ⟨m0 * 2 ^ (N - n), mul_pos hm0 (pow_pos (by decide) _), hsz, ?_⟩
  exact pair_shift hn hA hB
