import FormalConjectures.Util.ProblemImports

open Nat List Set

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
A358340: $a(n)$ is the smallest $n$-digit number whose fourth power is zeroless.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  sInf S

/--
A358340 It has been proved that there exist infinitely many zeroless squares and cubes but there is apparently no proof for 4th powers, 5th powers, etc.

Formalized as the conjecture that the set of natural numbers whose fourth power is zeroless is infinite.
-/
lemma is_zeroless_zero : is_zeroless 0 := by
  simp [is_zeroless, Nat.digits_zero]

lemma is_zeroless_one : is_zeroless 1 := by
  unfold is_zeroless
  rw [Nat.digits_of_lt 10 1 (by decide) (by decide)]
  simp

lemma is_zeroless_concat {a b n : ℕ}
    (ha : is_zeroless a) (hb : is_zeroless b)
    (hlen : (Nat.digits 10 b).length = n) :
    is_zeroless (b + 10 ^ n * a) := by
  have heq : Nat.digits 10 (b + 10 ^ n * a) =
      Nat.digits 10 b ++ Nat.digits 10 a := by
    simpa [hlen] using
      (Nat.digits_append_digits (b := 10) (m := a) (n := b) (by decide)).symm
  unfold is_zeroless
  rw [heq, List.mem_append]
  rintro (h | h)
  · exact hb h
  · exact ha h

lemma is_zeroless_of_ofDigits (L : List ℕ)
    (h1 : ∀ d ∈ L, d < 10) (h2 : ∀ d ∈ L, d ≠ 0)
    (h3 : ∀ h : L ≠ [], L.getLast h ≠ 0) :
    is_zeroless (Nat.ofDigits 10 L) := by
  unfold is_zeroless
  rw [Nat.digits_ofDigits 10 (by decide) L h1 h3]
  intro mem
  exact (h2 0 mem) rfl

lemma zl_pow4_of_ofDigits (m : ℕ) (L : List ℕ)
    (heq : m ^ 4 = Nat.ofDigits 10 L)
    (h1 : ∀ d ∈ L, d < 10) (h2 : ∀ d ∈ L, d ≠ 0)
    (h3 : ∀ h : L ≠ [], L.getLast h ≠ 0) :
    is_zeroless (m ^ 4) := by
  rw [heq]
  exact is_zeroless_of_ofDigits L h1 h2 h3

lemma zl_1 : is_zeroless (1 ^ 4) := by simpa using is_zeroless_one

lemma zl_2 : is_zeroless (2 ^ 4) :=
  zl_pow4_of_ofDigits 2 [6, 1] (by decide) (by decide) (by decide) (by decide)

lemma zl_3 : is_zeroless (3 ^ 4) :=
  zl_pow4_of_ofDigits 3 [1, 8] (by decide) (by decide) (by decide) (by decide)

lemma zl_4 : is_zeroless (4 ^ 4) :=
  zl_pow4_of_ofDigits 4 [6, 5, 2] (by decide) (by decide) (by decide) (by decide)

lemma zl_5 : is_zeroless (5 ^ 4) :=
  zl_pow4_of_ofDigits 5 [5, 2, 6] (by decide) (by decide) (by decide) (by decide)

lemma zl_6 : is_zeroless (6 ^ 4) :=
  zl_pow4_of_ofDigits 6 [6, 9, 2, 1] (by decide) (by decide) (by decide) (by decide)

lemma zl_11 : is_zeroless (11 ^ 4) :=
  zl_pow4_of_ofDigits 11 [1, 4, 6, 4, 1] (by decide) (by decide) (by decide) (by decide)

instance instDecidablePred_is_zeroless : DecidablePred is_zeroless :=
  fun k => inferInstanceAs (Decidable (0 ∉ Nat.digits 10 k))

/-- A positive integer has exactly `k` decimal digits iff `10^(k-1) ≤ n < 10^k`. -/
lemma digits_len_eq {n k : ℕ} (hn : n ≠ 0) (hk : 1 ≤ k) :
    (Nat.digits 10 n).length = k ↔ 10 ^ (k - 1) ≤ n ∧ n < 10 ^ k := by
  have hb : 1 < 10 := by decide
  rw [Nat.digits_len 10 n hb hn]
  cases k with
  | zero => omega
  | succ k =>
    have : log 10 n + 1 = k + 1 ↔ log 10 n = k := by omega
    rw [this, Nat.log_eq_iff (Or.inr ⟨hb, hn⟩)]
    simp

lemma digits_len_eq_of_pow_le {n k : ℕ} (h1 : 10 ^ k ≤ n) (h2 : n < 10 ^ (k + 1)) :
    (Nat.digits 10 n).length = k + 1 := by
  have hn : n ≠ 0 := by
    have : 0 < 10 ^ k := Nat.pow_pos (by decide)
    omega
  rw [digits_len_eq hn (by omega)]
  exact ⟨h1, h2⟩

/-- Digits of a concatenation `low + 10^k * high` when `low` has exactly `k` digits. -/
lemma digits_concat_eq {low high k : ℕ} (hlen : (Nat.digits 10 low).length = k) :
    Nat.digits 10 (low + 10 ^ k * high) = Nat.digits 10 low ++ Nat.digits 10 high := by
  simpa [hlen] using
    (Nat.digits_append_digits (b := 10) (m := high) (n := low) (by decide)).symm

lemma digits_concat_length {low high k : ℕ} (hlen : (Nat.digits 10 low).length = k) :
    (Nat.digits 10 (low + 10 ^ k * high)).length =
      k + (Nat.digits 10 high).length := by
  rw [digits_concat_eq hlen, List.length_append, hlen]

/-- Concatenate five zeroless blocks of common length `k`. -/
lemma is_zeroless_concat5 {A B C D E k : ℕ}
    (hA : is_zeroless A) (hB : is_zeroless B) (hC : is_zeroless C)
    (hD : is_zeroless D) (hE : is_zeroless E)
    (hBlen : (Nat.digits 10 B).length = k)
    (hClen : (Nat.digits 10 C).length = k)
    (hDlen : (Nat.digits 10 D).length = k)
    (hElen : (Nat.digits 10 E).length = k) :
    is_zeroless (E + 10 ^ k * D + 10 ^ (2 * k) * C + 10 ^ (3 * k) * B + 10 ^ (4 * k) * A) := by
  set w1 : ℕ := E + 10 ^ k * D
  have hw1 : is_zeroless w1 := is_zeroless_concat hD hE hElen
  have lw1 : (Nat.digits 10 w1).length = k + k := by
    simpa [w1, hDlen] using digits_concat_length (low := E) (high := D) hElen
  set w2 : ℕ := w1 + 10 ^ (k + k) * C
  have hw2 : is_zeroless w2 := by
    simpa [w2, two_mul] using is_zeroless_concat (a := C) (b := w1) (n := k + k) hC hw1 lw1
  have lw2 : (Nat.digits 10 w2).length = k + k + k := by
    simpa [w2, hClen] using digits_concat_length (low := w1) (high := C) lw1
  set w3 : ℕ := w2 + 10 ^ (k + k + k) * B
  have hw3 : is_zeroless w3 := by
    have : k + k + k = 3 * k := by ring
    simpa [w3, this] using
      is_zeroless_concat (a := B) (b := w2) (n := k + k + k) hB hw2 lw2
  have lw3 : (Nat.digits 10 w3).length = k + k + k + k := by
    simpa [w3, hBlen] using digits_concat_length (low := w2) (high := B) lw2
  set w4 : ℕ := w3 + 10 ^ (k + k + k + k) * A
  have hw4 : is_zeroless w4 := by
    have : k + k + k + k = 4 * k := by ring
    simpa [w4, this] using
      is_zeroless_concat (a := A) (b := w3) (n := k + k + k + k) hA hw3 lw3
  have : E + 10 ^ k * D + 10 ^ (2 * k) * C + 10 ^ (3 * k) * B + 10 ^ (4 * k) * A = w4 := by
    simp [w4, w3, w2, w1]
    ring
  rw [this]
  exact hw4

/-- Pairing: if the five binomial blocks are zeroless of common length `k`,
then `(m * 10^k + r)^4` is zeroless. -/
lemma is_zeroless_pairing {m r k : ℕ}
    (hm : is_zeroless (m ^ 4))
    (h0 : is_zeroless (r ^ 4))
    (h1 : is_zeroless (4 * m ^ 3 * r))
    (h2 : is_zeroless (6 * m ^ 2 * r ^ 2))
    (h3 : is_zeroless (4 * m * r ^ 3))
    (l0 : (Nat.digits 10 (r ^ 4)).length = k)
    (l1 : (Nat.digits 10 (4 * m * r ^ 3)).length = k)
    (l2 : (Nat.digits 10 (6 * m ^ 2 * r ^ 2)).length = k)
    (l3 : (Nat.digits 10 (4 * m ^ 3 * r)).length = k) :
    is_zeroless ((m * 10 ^ k + r) ^ 4) := by
  have hexp : (m * 10 ^ k + r) ^ 4 =
      r ^ 4 + 10 ^ k * (4 * m * r ^ 3) + 10 ^ (2 * k) * (6 * m ^ 2 * r ^ 2) +
        10 ^ (3 * k) * (4 * m ^ 3 * r) + 10 ^ (4 * k) * (m ^ 4) := by
    ring
  rw [hexp]
  exact is_zeroless_concat5 hm h1 h2 h3 h0 l3 l2 l1 l0

lemma two_mul_le_ten_pow (k : ℕ) (hk : 1 ≤ k) : 2 * k ≤ 10 ^ k := by
  induction k with
  | zero => cases hk
  | succ k ih =>
    cases k with
    | zero => decide
    | succ k =>
      have ih' : 2 * (k + 1) ≤ 10 ^ (k + 1) := ih (by omega)
      have h2 : 2 ≤ 10 ^ (k + 1) :=
        Nat.le_trans (by decide : (2 : ℕ) ≤ 10)
          (Nat.le_self_pow (by omega) 10)
      calc
        2 * (k + 1 + 1) = 2 * (k + 1) + 2 := by ring
        _ ≤ 10 ^ (k + 1) + 2 := Nat.add_le_add_right ih' 2
        _ ≤ 10 ^ (k + 1) + 10 ^ (k + 1) := Nat.add_le_add_left h2 _
        _ = 2 * 10 ^ (k + 1) := by ring
        _ ≤ 10 * 10 ^ (k + 1) := Nat.mul_le_mul_right _ (by decide)
        _ = 10 ^ (k + 1 + 1) := by simp [pow_succ, mul_comm]

/-- Center: one more than `⌊10^n / √3⌋`. -/
def m0 (n : ℕ) : ℕ := Nat.sqrt (10 ^ (2 * n) / 3) + 1

lemma m0_pos (n : ℕ) : 0 < m0 n := by
  unfold m0
  omega

lemma m1_ge_half (n : ℕ) (hn : 1 ≤ n) :
    10 ^ n / 2 ≤ Nat.sqrt (10 ^ (2 * n) / 3) := by
  rw [Nat.le_sqrt]
  have h2 : 2 ∣ 10 ^ n := by
    have : 2 ∣ 10 := by decide
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    exact Dvd.dvd.mul_left this _
  have hsq : 10 ^ n / 2 * (10 ^ n / 2) = 10 ^ (2 * n) / 4 := by
    rw [Nat.div_mul_div_comm h2 h2, ← pow_add]
    simp [two_mul]
  have hle : 10 ^ (2 * n) / 4 ≤ 10 ^ (2 * n) / 3 :=
    Nat.div_le_div_left (by decide) (by decide)
  exact hsq.le.trans hle

/-- `T` search window. -/
def Tpar (n : ℕ) : ℕ := 10 ^ (4 * n / 5)

lemma Tpar_pos (n : ℕ) : 0 < Tpar n :=
  Nat.pow_pos (by decide)

lemma exists_t_zl (n : ℕ) (hn : 1 ≤ n) :
    ∃ t, t < Tpar n ∧ is_zeroless ((m0 n + t) ^ 4) := by
  -- For every `n ≥ 1` the short interval around `10^n / √3` contains a
  -- zeroless fourth power; this is the remaining analytic/constructive step.
  sorry

lemma exists_zl_pow4_gt (M : ℕ) : ∃ m, M < m ∧ is_zeroless (m ^ 4) := by
  let n := max (M + 3) 1
  have hn1 : 1 ≤ n := le_max_right _ _
  have hm1 : M < Nat.sqrt (10 ^ (2 * n) / 3) := by
    have hhalf : 10 ^ n / 2 ≤ Nat.sqrt (10 ^ (2 * n) / 3) := m1_ge_half n hn1
    have hnM : M + 3 ≤ n ∨ n = 1 := by
      have := le_max_left (M + 3) 1
      omega
    have hMn : M + 1 ≤ n := by omega
    have hnT : n ≤ 10 ^ n / 2 := by
      have : 2 * n ≤ 10 ^ n := two_mul_le_ten_pow n hn1
      exact (Nat.le_div_iff_mul_le (by decide)).2 (by simpa [mul_comm] using this)
    exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self M) (hMn.trans hnT)) hhalf
  obtain ⟨t, ht, hzl⟩ := exists_t_zl n hn1
  refine ⟨m0 n + t, ?_, hzl⟩
  unfold m0
  omega

theorem oeis_a358340_conjecture_k4 :
    Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  refine Set.infinite_of_not_bddAbove ?_
  intro ⟨M, hM⟩
  obtain ⟨m, hm, hzl⟩ := exists_zl_pow4_gt M
  have : m ∈ { m : ℕ | is_zeroless (m ^ 4) } := hzl
  exact (not_le_of_gt hm (hM this)).elim
