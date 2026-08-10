import FormalConjectures.Util.ProblemImports

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

/- ### Auxiliary development

The predicate `is_evil` inside `a` is exactly the following standalone Boolean function,
which asks whether `k` has an even number of binary `1`-digits. -/

/-- The internal `is_evil` predicate of `a`, as a standalone function. -/
def isEvil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

/-- Base case of the bounded search: once `m > n`, `find_min_m` returns `0`. -/
theorem fbase (n : ℕ) (ie : ℕ → Bool) (m : ℕ) (hm : m > n) :
    a.find_min_m n ie m = 0 := by
  rw [a.find_min_m.eq_def]; simp [hm]

/-- Recursion step of the bounded search: if `m ≤ n` and `C(n,m)` is not evil,
then `find_min_m` at `m` agrees with `find_min_m` at `m+1`. -/
theorem fstep (n : ℕ) (ie : ℕ → Bool) (m : ℕ) (hm : ¬ m > n)
    (hev : ie (n.choose m) = false) (hnext : a.find_min_m n ie (m+1) = 0) :
    a.find_min_m n ie m = 0 := by
  rw [a.find_min_m.eq_def]; simp only [hm, if_false, hev, Bool.false_eq_true]
  exact hnext

/-- If `k` has an odd number of one-bits then `isEvil k = false` (`k` is odious). -/
theorem evF (k c : ℕ) (h : (Nat.bits k).count true = c) (hc : c % 2 = 1) :
    isEvil k = false := by
  simp only [isEvil, h]; simp [hc]

/- Population counts of the binomial coefficients occurring in rows `0,1,2,7,8`.
Each is computed from the binary expansion via `Nat.bits_append_bit`. -/

theorem bc1 : (Nat.bits 1).count true = 1 := by
  have hd : (1:ℕ) = Nat.bit true 0 := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc2 : (Nat.bits 2).count true = 1 := by
  have hd : (2:ℕ) = Nat.bit false (Nat.bit true 0) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc7 : (Nat.bits 7).count true = 3 := by
  have hd : (7:ℕ) = Nat.bit true (Nat.bit true (Nat.bit true 0)) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc8 : (Nat.bits 8).count true = 1 := by
  have hd : (8:ℕ) = Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true 0))) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc21 : (Nat.bits 21).count true = 3 := by
  have hd : (21:ℕ) = Nat.bit true (Nat.bit false (Nat.bit true (Nat.bit false (Nat.bit true 0)))) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc28 : (Nat.bits 28).count true = 3 := by
  have hd : (28:ℕ) = Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit true 0)))) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc35 : (Nat.bits 35).count true = 3 := by
  have hd : (35:ℕ) = Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true 0))))) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc56 : (Nat.bits 56).count true = 3 := by
  have hd : (56:ℕ) = Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit true 0))))) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

theorem bc70 : (Nat.bits 70).count true = 3 := by
  have hd : (70:ℕ) = Nat.bit false (Nat.bit true (Nat.bit true (Nat.bit false (Nat.bit false (Nat.bit false (Nat.bit true 0)))))) := by decide
  rw [hd]; repeat rw [Nat.bits_append_bit _ _ (by decide)]
  simp

/-- Convenience wrapper: `C(n,m)` is not evil, given its value `v` and odd popcount `c`. -/
theorem hevC (n m v c : ℕ) (hv : Nat.choose n m = v)
    (hb : (Nat.bits v).count true = c) (hc : c % 2 = 1) :
    isEvil (Nat.choose n m) = false := by
  rw [hv]; exact evF v c hb hc

/- The five known "all-odious" rows: `a n = 0` for `n ∈ {0,1,2,7,8}`. -/

theorem a0 : a 0 = 0 := by
  show a.find_min_m 0 isEvil 1 = 0
  exact fbase 0 isEvil 1 (by norm_num)

theorem a1 : a 1 = 0 := by
  show a.find_min_m 1 isEvil 1 = 0
  refine fstep 1 isEvil 1 (by norm_num) (hevC 1 1 1 1 (by decide) bc1 (by decide)) ?_
  exact fbase 1 isEvil 2 (by norm_num)

theorem a2 : a 2 = 0 := by
  show a.find_min_m 2 isEvil 1 = 0
  refine fstep 2 isEvil 1 (by norm_num) (hevC 2 1 2 1 (by decide) bc2 (by decide)) ?_
  refine fstep 2 isEvil 2 (by norm_num) (hevC 2 2 1 1 (by decide) bc1 (by decide)) ?_
  exact fbase 2 isEvil 3 (by norm_num)

theorem a7 : a 7 = 0 := by
  show a.find_min_m 7 isEvil 1 = 0
  refine fstep 7 isEvil 1 (by norm_num) (hevC 7 1 7 3 (by decide) bc7 (by decide)) ?_
  refine fstep 7 isEvil 2 (by norm_num) (hevC 7 2 21 3 (by decide) bc21 (by decide)) ?_
  refine fstep 7 isEvil 3 (by norm_num) (hevC 7 3 35 3 (by decide) bc35 (by decide)) ?_
  refine fstep 7 isEvil 4 (by norm_num) (hevC 7 4 35 3 (by decide) bc35 (by decide)) ?_
  refine fstep 7 isEvil 5 (by norm_num) (hevC 7 5 21 3 (by decide) bc21 (by decide)) ?_
  refine fstep 7 isEvil 6 (by norm_num) (hevC 7 6 7 3 (by decide) bc7 (by decide)) ?_
  refine fstep 7 isEvil 7 (by norm_num) (hevC 7 7 1 1 (by decide) bc1 (by decide)) ?_
  exact fbase 7 isEvil 8 (by norm_num)

theorem a8 : a 8 = 0 := by
  show a.find_min_m 8 isEvil 1 = 0
  refine fstep 8 isEvil 1 (by norm_num) (hevC 8 1 8 1 (by decide) bc8 (by decide)) ?_
  refine fstep 8 isEvil 2 (by norm_num) (hevC 8 2 28 3 (by decide) bc28 (by decide)) ?_
  refine fstep 8 isEvil 3 (by norm_num) (hevC 8 3 56 3 (by decide) bc56 (by decide)) ?_
  refine fstep 8 isEvil 4 (by norm_num) (hevC 8 4 70 3 (by decide) bc70 (by decide)) ?_
  refine fstep 8 isEvil 5 (by norm_num) (hevC 8 5 56 3 (by decide) bc56 (by decide)) ?_
  refine fstep 8 isEvil 6 (by norm_num) (hevC 8 6 28 3 (by decide) bc28 (by decide)) ?_
  refine fstep 8 isEvil 7 (by norm_num) (hevC 8 7 8 1 (by decide) bc8 (by decide)) ?_
  refine fstep 8 isEvil 8 (by norm_num) (hevC 8 8 1 1 (by decide) bc1 (by decide)) ?_
  exact fbase 8 isEvil 9 (by norm_num)

/-- If `n ≥ 1` is *evil* (even popcount), then `C(n,1) = n` is evil and `a n = 1`. -/
theorem a_eq_one (n : ℕ) (hn : 1 ≤ n) (h : isEvil n = true) : a n = 1 := by
  show a.find_min_m n isEvil 1 = 1
  rw [a.find_min_m.eq_def]
  have h1 : ¬ (1 > n) := by omega
  simp only [h1, if_false, Nat.choose_one_right, h, if_true]

/-! ### The power-of-two subcase

We can additionally settle the case `n = 2^k` with `k` even.  Here
`C(2^k, 2) = 2^{k-1}(2^k-1)`, whose binary representation is a block of `k` ones
shifted left by `k-1`, hence has population count exactly `k`.  For even `k` this
is an *evil* entry, so `a(2^k) = 2`.  This is one of the few cases where the
digit-sum parity of a binomial coefficient `C(n,m)` with `m ≥ 2` is elementarily
computable for a whole infinite family of `n`. -/

/-- `Nat.bits (2^k - 1)` is a list of `k` ones. -/
theorem bits_pow2_sub1 (k : ℕ) : Nat.bits (2 ^ k - 1) = List.replicate k true := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hb : Nat.bit true (2 ^ n - 1) = 2 * (2 ^ n - 1) + 1 := by simp [Nat.bit]
    have h2 : 2 ^ (n + 1) - 1 = Nat.bit true (2 ^ n - 1) := by
      rw [hb, pow_succ]; have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega
    rw [h2, Nat.bits_append_bit _ true (by simp), ih]; rfl

/-- Multiplying by `2^j` prepends `j` zero bits. -/
theorem bits_mul_pow2 (j m : ℕ) (hm : 0 < m) :
    Nat.bits (2 ^ j * m) = List.replicate j false ++ Nat.bits m := by
  induction j with
  | zero => simp
  | succ i ih =>
    have hpos : 0 < 2 ^ i * m := Nat.mul_pos (pow_pos (by norm_num) i) hm
    have h2 : 2 ^ (i + 1) * m = Nat.bit false (2 ^ i * m) := by
      have hbf : Nat.bit false (2 ^ i * m) = 2 * (2 ^ i * m) := by simp [Nat.bit]
      rw [hbf, pow_succ]; ring
    rw [h2, Nat.bits_append_bit _ false (fun h => absurd h hpos.ne'), ih]; rfl

theorem bits_one : Nat.bits 1 = [true] := by
  have := bits_pow2_sub1 1; simpa using this

/-- The population count of `2^k` is `1`. -/
theorem popcount_pow2 (k : ℕ) : (Nat.bits (2 ^ k)).count true = 1 := by
  have h : (2 : ℕ) ^ k = 2 ^ k * 1 := by ring
  rw [h, bits_mul_pow2 k 1 (by norm_num), bits_one]
  simp [List.count_append, List.count_replicate]

/-- The population count of `C(2^k, 2)` is exactly `k`. -/
theorem popcount_C_pow2_two (k : ℕ) (hk : 1 ≤ k) :
    (Nat.bits (Nat.choose (2 ^ k) 2)).count true = k := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hchoose : Nat.choose (2 ^ k) 2 = 2 ^ (k - 1) * (2 ^ k - 1) := by
    rw [Nat.choose_two_right]
    have key : 2 ^ k * (2 ^ k - 1) = 2 * (2 ^ (k - 1) * (2 ^ k - 1)) := by
      have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        rw [pow_succ]; ring
      rw [hk2]; ring
    rw [key, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hchoose, bits_mul_pow2 (k - 1) (2 ^ k - 1) (by omega), bits_pow2_sub1]
  simp [List.count_append, List.count_replicate]

/-- For even `k ≥ 2`, `a(2^k) = 2`: the entry `C(2^k, 2)` is the first evil one. -/
theorem a_pow2_even (k : ℕ) (hk : 2 ≤ k) (hev : k % 2 = 0) : a (2 ^ k) = 2 := by
  show a.find_min_m (2 ^ k) isEvil 1 = 2
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hev1 : isEvil (Nat.choose (2 ^ k) 1) = false := by
    rw [Nat.choose_one_right]; simp only [isEvil, popcount_pow2]; decide
  have hev2 : isEvil (Nat.choose (2 ^ k) 2) = true := by
    simp only [isEvil, popcount_C_pow2_two k (by omega), hev]; decide
  rw [a.find_min_m.eq_def]
  simp only [show ¬ (1 > 2 ^ k) by omega, if_false, hev1, Bool.false_eq_true]
  rw [a.find_min_m.eq_def]
  simp only [show ¬ (2 > 2 ^ k) by omega, if_false, hev2, if_true]

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · -- Forward direction.  We argue by contradiction on `n ∉ {0,1,2,7,8}`.
    intro h
    by_contra hns
    by_cases he : isEvil n = true
    · -- Case `n` evil: then `C(n,1) = n` is evil, so `a n = 1 ≠ 0`, contradicting `a n = 0`.
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exfalso; apply hns; subst h0; decide
        · exact h0
      have h1 := a_eq_one n hn1 he
      rw [h] at h1
      exact absurd h1 (by decide)
    · -- Case `n` odious (`isEvil n = false`): we must exhibit an evil binomial in row `n`.
      --
      -- This is the genuinely open core of OEIS A249609.  It is equivalent to the assertion
      -- that for every odious `n ∉ {1,2,7,8}` the `n`-th row of Pascal's triangle contains a
      -- binomial coefficient with an even number of binary digits.  The only binomial whose
      -- digit-sum parity is elementarily computable for general `n` is `C(n,1) = n` itself;
      -- controlling the digit sum of `C(n,m)` for `m ≥ 2` uniformly in `n` is a Gelfond-type
      -- problem on digit sums of polynomial sequences, for which no elementary (formalizable)
      -- proof is currently known.
      --
      -- We can at least dispatch the infinite family `n = 2^k` with `k` even (`k ≥ 2`), where
      -- `C(2^k,2)` has population count `k`, hence is evil, giving `a(2^k) = 2 ≠ 0`.
      by_cases hpow : ∃ k, n = 2 ^ k ∧ 2 ≤ k ∧ k % 2 = 0
      · obtain ⟨k, rfl, hk2, hke⟩ := hpow
        have hval := a_pow2_even k hk2 hke
        rw [h] at hval
        exact absurd hval (by norm_num)
      · sorry
  · -- Reverse direction: direct evaluation of `a` at the five exceptional values.
    intro h
    fin_cases h
    · exact a0
    · exact a1
    · exact a2
    · exact a7
    · exact a8
