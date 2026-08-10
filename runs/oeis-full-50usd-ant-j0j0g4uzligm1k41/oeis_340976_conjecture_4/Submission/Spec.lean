import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A340976: Sum_{1 < k < n} sigma(n) mod k, where $\sigma = \sigma_1$ is the sum of divisors function (A000203).
$$a(n) = \sum_{1 < k < n} \left( \sigma_1(n) \bmod k \right)$$
-/
def a (n : ℕ) : ℕ :=
  let sigma1_n : ℕ := n.divisors.sum id
  (Ioo 1 n).sum fun k : ℕ => sigma1_n % k

/-- Cast of a natural number to `ZMod 2` is `1` when odd and `0` when even. -/
private theorem cast_two_eq (k : ℕ) : (k : ZMod 2) = if k % 2 = 1 then 1 else 0 := by
  have h : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  rw [h]
  rcases Nat.even_or_odd k with he | ho
  · rw [Nat.even_iff] at he; rw [if_neg (by omega), he]; simp
  · rw [Nat.odd_iff] at ho; rw [if_pos ho, ho]; simp

private theorem term_eq (s k : ℕ) : ((k : ZMod 2) * (s / k : ℕ) : ZMod 2)
    = if k % 2 = 1 then ((s / k : ℕ) : ZMod 2) else 0 := by
  rw [cast_two_eq k]; by_cases h : k % 2 = 1 <;> simp [h]

/-- **Exact parity characterization** of `a`.  Since `σ(n) % k = σ(n) - k⌊σ(n)/k⌋`,
one has `a n = (n-2)σ(n) - ∑_{2≤k<n} k⌊σ(n)/k⌋`, and reducing mod `2` (only odd `k`
survive in the second sum) yields the closed form below.  This is a genuine,
machine-verified reduction of the parity of `a n` to a divisor-floor sum. -/
theorem a_parity (n : ℕ) :
    a n % 2 = ((n + 1) * (n.divisors.sum id) +
      ∑ k ∈ (range n).filter (fun k => k % 2 = 1), (n.divisors.sum id) / k) % 2 := by
  set s := n.divisors.sum id with hs
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> (simp only [a, hs]; decide)
  · suffices h : (a n : ZMod 2)
        = (((n + 1) * s + ∑ k ∈ (range n).filter (fun k => k % 2 = 1), s / k : ℕ) : ZMod 2) by
      exact (ZMod.natCast_eq_natCast_iff _ _ 2).mp h
    have ha : a n = ∑ k ∈ Ioo 1 n, s % k := rfl
    rw [ha]
    push_cast
    rw [Nat.cast_sum]
    have hterm : ∀ k ∈ Ioo 1 n, ((s % k : ℕ) : ZMod 2)
        = (s : ZMod 2) - (k : ZMod 2) * ((s / k : ℕ) : ZMod 2) := by
      intro k _
      have hle : k * (s / k) ≤ s := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self s k
      have : s % k = s - k * (s / k) := by
        have := Nat.div_add_mod s k; omega
      rw [this, Nat.cast_sub hle]; push_cast; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const]
    rw [Finset.sum_congr rfl (fun k _ => term_eq s k), ← Finset.sum_filter]
    rw [Nat.card_Ioo]
    have hsfold : (∑ x ∈ n.divisors, (↑(id x) : ZMod 2)) = (s : ZMod 2) := by
      rw [hs, Nat.cast_sum]
    rw [hsfold]
    have hins : (range n).filter (fun k => k % 2 = 1)
        = insert 1 ((Ioo 1 n).filter (fun k => k % 2 = 1)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp [Finset.mem_filter, Finset.mem_Ioo]), Nat.div_one]
    rw [nsmul_eq_mul]
    have hcast : ((n - 1 - 1 : ℕ) : ZMod 2) = (n : ZMod 2) := by
      have h2 : n - 1 - 1 = n - 2 := by omega
      rw [h2, Nat.cast_sub hn, show ((2 : ℕ) : ZMod 2) = 0 by decide, sub_zero]
    rw [hcast, CharTwo.sub_eq_add]
    have expand : ((n : ZMod 2) + 1) * (s : ZMod 2)
        + ((s : ZMod 2) + ∑ x ∈ (Ioo 1 n).filter (fun k => k % 2 = 1), ((s / x : ℕ) : ZMod 2))
        = (n : ZMod 2) * (s : ZMod 2) + ((s : ZMod 2) + (s : ZMod 2))
          + ∑ x ∈ (Ioo 1 n).filter (fun k => k % 2 = 1), ((s / x : ℕ) : ZMod 2) := by ring
    rw [expand, CharTwo.add_self_eq_zero]
    ring

/--
oeis_340976_conjecture_4:
4) What is the frequency of odd vs. even terms? a(n) is odd for consecutive indices 21..22, 35..49, 51..56, 58..61, 64..69, 73..79, ...: Are there patterns or simple subsequence(s) of such runs of two or larger?

Formalization: There exist arbitrarily long runs of consecutive natural numbers $n$ such that $a(n)$ is odd.
-/
theorem oeis_340976_conjecture_4 :
  ∀ L : ℕ, L ≥ 2 → ∃ N : ℕ, ∀ i : ℕ, i < L → a (N + i) % 2 = 1 := by sorry

