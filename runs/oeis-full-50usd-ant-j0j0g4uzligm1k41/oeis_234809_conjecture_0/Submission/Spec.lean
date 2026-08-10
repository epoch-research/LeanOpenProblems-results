import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A234809: $a(n) = |\{0 < k < n: p = k + \phi(n-k) \text{ and } 2(n-p) + 1 \text{ are both prime}\}|$,
where $\phi(\cdot)$ is Euler's totient function.
-/
noncomputable def A234809 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k : ℕ =>
    let p : ℕ := k + Nat.totient (n - k)
    if Nat.Prime p ∧ Nat.Prime (2 * (n - p) + 1) then 1 else 0

/-- **Reduction lemma** (fully proven): to show `A234809 n > 0` it suffices to exhibit a
single `k` with `1 ≤ k < n` for which both primality conditions hold. This isolates the
entire mathematical content of the conjecture into a clean existence statement. -/
theorem A234809_pos_of_exists (n : ℕ)
    (h : ∃ k, 1 ≤ k ∧ k < n ∧ Nat.Prime (k + Nat.totient (n - k)) ∧
              Nat.Prime (2 * (n - (k + Nat.totient (n - k))) + 1)) :
    A234809 n > 0 := by
  obtain ⟨k, hk1, hk2, hp, hp2⟩ := h
  unfold A234809
  apply Finset.sum_pos'
  · intro i _; positivity
  · refine ⟨k, Finset.mem_Ico.mpr ⟨hk1, hk2⟩, ?_⟩
    simp only [hp, hp2, and_self, if_true]; norm_num

/-- The precise open core: for every `n > 2` there is a witness `k`.  By
`A234809_pos_of_exists` this is equivalent to the conjecture.  Note that any such witness `k`
yields primes `q = k + φ(n-k)` and `r = 2·(n - q) + 1` with `2·q + r = 2·n + 1`, i.e. a
*Lemoine representation* of the odd number `2·n + 1`.  Hence establishing this for all `n > 2`
proves Lemoine's conjecture (every odd number `≥ 7` is `2·prime + prime`), open since 1894. -/
theorem A234809_exists_witness (n : ℕ) (hn : n > 2) :
    ∃ k, 1 ≤ k ∧ k < n ∧ Nat.Prime (k + Nat.totient (n - k)) ∧
         Nat.Prime (2 * (n - (k + Nat.totient (n - k))) + 1) := by
  sorry

/-- Conjecture: a(n) > 0 for all n > 2. -/
theorem oeis_234809_conjecture_0 (n : ℕ) (hn : n > 2) : A234809 n > 0 :=
  A234809_pos_of_exists n (A234809_exists_witness n hn)
