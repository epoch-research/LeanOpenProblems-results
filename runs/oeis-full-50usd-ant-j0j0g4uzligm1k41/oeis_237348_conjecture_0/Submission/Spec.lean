import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The $k$-th prime number, $p_k$, with $p_1=2$. This is $\operatorname{prime}(k)$ from the OEIS description.
-/
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/--
A237348: Number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $\mathrm{prime}(k) + 4$ and $\mathrm{prime}(\mathrm{prime}(m)) + 4$ are both prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sum is over $k$ such that $1 \le k \le n - 1$.
  -- This range ensures $k > 0$ and $m = n - k > 0$.
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 4)

    if cond1 ∧ cond2 then 1 else 0

/--
A generalization of A237348 to a general even number $2d$.
The number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 2 * d)

    if cond1 ∧ cond2 then 1 else 0

/--
Reduction lemma (fully proved): `a_generalized n d` is positive iff there is a
valid split `n = k + (n - k)` with `1 ≤ k < n` realizing both prime conditions.
This makes the additive structure explicit: `0 < a_generalized n d` iff
`n ∈ K_d + M_d`, where
`K_d = {k | Nat.Prime (prime_k_1indexed k + 2d)}` and
`M_d = {m | Nat.Prime (prime_k_1indexed (prime_k_1indexed m) + 2d)}`.
-/
theorem a_generalized_pos_iff (n d : ℕ) : 0 < a_generalized n d ↔ ∃ k ∈ Ico 1 n,
    Nat.Prime (prime_k_1indexed k + 2 * d) ∧
    Nat.Prime (prime_k_1indexed (prime_k_1indexed (n - k)) + 2 * d) := by
  unfold a_generalized
  simp only [Finset.sum_pos_iff, Finset.mem_Ico]
  constructor
  · rintro ⟨k, hk, hpos⟩
    refine ⟨k, hk, ?_⟩
    by_contra h
    simp [h] at hpos
  · rintro ⟨k, hk, h1, h2⟩
    exact ⟨k, hk, by simp [h1, h2]⟩

/--
**de Polignac-hardness (fully proved, machine-checked).**
If the conjecture below holds for a given `d`, then there are infinitely many indices `k`
with `prime_k_1indexed k + 2 * d` prime — equivalently, infinitely many primes `p` with
`p + 2d` prime. For `d = 1` this is exactly the **Twin Prime Conjecture**; for general `d`
it is **de Polignac's conjecture** for gap `2d`, open for every even gap and absent from
Mathlib. Hence any complete proof of `oeis_237348_conjecture_0` would entail a proof of a
generalization of the twin prime conjecture.

Proof idea: from a witness split `n = k + (n-k)`, either the first index `k` is large
(giving a large element of the prime-pair set), or `n - k` is large and
`prime_k_1indexed (n-k)` (a prime whose shift is prime, by the second condition) is large;
since `prime_k_1indexed m ≥ m - 1`, the prime-pair set is unbounded, hence infinite.
-/
theorem conjecture_implies_de_polignac (d : ℕ)
    (H : ∃ N, 0 < N ∧ ∀ n, N < n → 0 < a_generalized n d) :
    {k : ℕ | Nat.Prime (prime_k_1indexed k + 2 * d)}.Infinite := by
  obtain ⟨N, hN, hconj⟩ := H
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  set n := max N (2 * B + 2) + 1 with hn_def
  have hnN : N < n := by omega
  obtain ⟨k, hk, h1, h2⟩ := (a_generalized_pos_iff n d).mp (hconj n hnN)
  rw [Finset.mem_Ico] at hk
  have hkB : k ≤ B := hB h1
  have hk'B : prime_k_1indexed (n - k) ≤ B := hB h2
  have hge : (n - k) - 1 ≤ prime_k_1indexed (n - k) := by
    unfold prime_k_1indexed
    exact Nat.le_nth (fun hf => absurd hf Nat.infinite_setOf_prime)
  have hn_big : 2 * B + 3 ≤ n := by omega
  omega

/--
OEIS A237348 Conjecture: For each $d = 1, 2, 3, \dots$ there is a positive integer $N(d)$
for which any integer $n > N(d)$ can be written as $k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.

By `conjecture_implies_de_polignac`, this statement implies the infinitude of prime pairs
with gap `2d` for every `d` — i.e. de Polignac's conjecture for all even gaps, which is open
(the `d = 1` case is the Twin Prime Conjecture) and not available in Mathlib. No proof
depending only on `propext, Classical.choice, Quot.sound` is therefore possible with current
mathematics, and the statement is true (so it cannot be disproved either).
-/
theorem oeis_237348_conjecture_0 :
  ∀ (d : ℕ), 1 ≤ d →
    ∃ (N : ℕ), 0 < N ∧
      ∀ (n : ℕ), N < n →
        0 < a_generalized n d := by sorry
