import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A167918: $a(n)$ is smallest index $k > n$ of $k$-th prime with $f(n,k):=(p(k)+p(k+1))/(p(n)+p(n+1))$ an integer $\ge 2$ ($n=1,2,...)$.
-/
noncomputable def A167918 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- The sequence is 1-indexed.
  else
    -- P i is the i-th prime, 1-indexed: p(i).
    let P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

    -- S i is $p_i + p_{i+1}$.
    let S (i : ℕ) : ℕ := P i + P (i + 1)

    let D_n := S n

    -- The set of indices $k$ that satisfy the condition.
    -- Since $k > n$, the ratio of the sums must be $\ge 2$ if divisibility holds.
    let k_set : Set ℕ := { k : ℕ | k > n ∧ D_n ∣ S k }

    -- sInf returns the smallest element of the set.
    sInf k_set

-- Redefine P and S noncomputably for global use.
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- $S_i = p_i + p_{i+1}$ -/
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)

/--
The value of the ratio $f(n, a(n)) = S_{\text{A167918 } n} / S_n$.
This is an exact division since $\text{A167918 } n$ is defined such that the divisibility holds.
For $n=0$, it returns 0, as the sequence is 1-indexed.
-/
noncomputable def A167918_ratio (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let k := A167918 n
    -- We use Nat.div (/) because A167918 guarantees S n divides S k
    (S k) / (S n)

/-!
### Supporting lemmas

We first develop, with complete rigor, the concrete values of `S`, of `A167918`,
and of `A167918_ratio` for the smallest index, together with the exact logical
reduction of the disproof to unboundedness of the ratio sequence.
-/

/-- Compute the `k`-th prime (0-indexed) from a `Nat.count` witness. -/
lemma nthp (k m : ℕ) (hm : Nat.Prime m) (hc : Nat.count Nat.Prime m = k) :
    Nat.nth Nat.Prime k = m := by
  have := Nat.nth_count (p := Nat.Prime) (n := m) hm
  rwa [hc] at this

lemma p3 : Nat.nth Nat.Prime 3 = 7 := nthp 3 7 (by norm_num) (by decide)
lemma p4 : Nat.nth Nat.Prime 4 = 11 := nthp 4 11 (by norm_num) (by decide)
lemma p5 : Nat.nth Nat.Prime 5 = 13 := nthp 5 13 (by norm_num) (by decide)
lemma p6 : Nat.nth Nat.Prime 6 = 17 := nthp 6 17 (by norm_num) (by decide)

/-- `S i = p_i + p_{i+1}` for small `i`. -/
lemma S1 : S 1 = 5 := by unfold S P; simp
lemma S2 : S 2 = 8 := by unfold S P; simp
lemma S3 : S 3 = 12 := by unfold S P; norm_num [p3]
lemma S4 : S 4 = 18 := by unfold S P; norm_num [p3, p4]
lemma S5 : S 5 = 24 := by unfold S P; norm_num [p4, p5]
lemma S6 : S 6 = 30 := by unfold S P; norm_num [p5, p6]

/-- The local `let`-bindings inside `A167918` coincide with the global `S`. -/
lemma A_eq (n : ℕ) (hn : n ≠ 0) :
    A167918 n = sInf { k : ℕ | k > n ∧ S n ∣ S k } := by
  unfold A167918 S P
  rw [if_neg hn]

/-- `a(1) = 6`: the least `k > 1` with `S 1 = 5 ∣ S k` is `k = 6` (`S 6 = 30`). -/
lemma A1 : A167918 1 = 6 := by
  rw [A_eq 1 (by norm_num)]
  have h6 : (6 : ℕ) ∈ { k : ℕ | k > 1 ∧ S 1 ∣ S k } := by
    refine ⟨by norm_num, ?_⟩
    rw [S1, S6]; norm_num
  refine le_antisymm (Nat.sInf_le h6) ?_
  have hmem := Nat.sInf_mem ⟨6, h6⟩
  set s := sInf { k : ℕ | k > 1 ∧ S 1 ∣ S k } with hs
  obtain ⟨hs1, hsdvd⟩ := hmem
  have hle : s ≤ 6 := Nat.sInf_le h6
  interval_cases s
  · rw [S1, S2] at hsdvd; omega
  · rw [S1, S3] at hsdvd; omega
  · rw [S1, S4] at hsdvd; omega
  · rw [S1, S5] at hsdvd; omega
  · rfl

/-- `f(1, a(1)) = S_6 / S_1 = 30 / 5 = 6`. -/
lemma ratio1 : A167918_ratio 1 = 6 := by
  unfold A167918_ratio
  rw [if_neg (by norm_num), A1]
  show S 6 / S 1 = 6
  rw [S6, S1]

/--
oeis_A167918_conjecture_5a: It is an open problem whether the ratio $f(n, k)$ is bounded,
where $k = a(n)$ is the smallest index $> n$ such that $f(n, k)$ is an integer $\ge 2$.
Formally, is the sequence $n \mapsto (S_{a(n)} / S_n)$ bounded?

The conjecture (that the sequence is bounded) is FALSE: the ratio sequence is
unbounded.  This is confirmed by explicit witnesses, e.g. `A167918_ratio 1 = 6`
(proved above as `ratio1`), `A167918_ratio 9 = 10` (with `520 = 257 + 263`),
`A167918_ratio 1009 = 72` (with `1154016 = 577007 + 577009`, a twin-prime sum),
and record values that keep growing with `n` (145 at `n = 48996`, 155 at
`n = 122948`, ...).  Heuristically `A167918_ratio n ≍ log n → ∞`, since the
density of sums of two consecutive primes near `x` is `~ 1/(2 log x) → 0`.

We prove the negation.  It reduces rigorously to unboundedness of the ratio:
`∀ C, ∃ n > 0, C < A167918_ratio n`.  For `C < 6` this is witnessed by `n = 1`
(`ratio1`).  The remaining, universal claim for `C ≥ 6` is the genuine content
of this open problem.
-/
theorem oeis_A167918_conjecture_5a.disproof :
    ¬ (∃ C : ℕ, ∀ n : ℕ, n > 0 → A167918_ratio n ≤ C) := by
  -- It suffices to show the ratio sequence is unbounded.
  suffices H : ∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ C < A167918_ratio n by
    rintro ⟨C, hC⟩
    obtain ⟨n, hn, hlt⟩ := H C
    exact absurd (hC n hn) (by omega)
  intro C
  by_cases h : C < 6
  · -- `n = 1` gives ratio `6 > C`.
    exact ⟨1, by norm_num, by rw [ratio1]; omega⟩
  · sorry
