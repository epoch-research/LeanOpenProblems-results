import FormalConjectures.Util.ProblemImports
open Function

/--
A212844: $a(n) = 2^{n+2} \bmod n$.
Since the OEIS sequence starts at $n=1$, the Lean function $a(n)$ returns the $(n+1)$-th term of the sequence.
The $(n+1)$-th term is calculated by substituting $n+1$ into $2^{n+2} \bmod n$.
-/
def a : ℕ → ℕ
| 0     => 0
| (n+1) => (2 ^ ((n + 1) + 2)) % (n + 1)

/-!
### Reduction of the conjecture

`a n` for `n ≥ 1` is `2 ^ (n + 2) % n`, and `a 0 = 0`.  The following lemma
records the elementary sufficient condition for `a n = k`: if `n ≥ 1`, `k < n`
and `2 ^ (n + 2) ≡ k [MOD n]`, then `a n = k`.  Consequently the surjectivity of
`a` is equivalent to the arithmetic existence statement

`∀ k, ∃ n, 0 < n ∧ k < n ∧ 2 ^ (n + 2) ≡ k [MOD n]`,

which is precisely the content of the A212844 conjecture.
-/

/-- If `n ≥ 1`, `k < n` and `2 ^ (n + 2) ≡ k [MOD n]`, then `a n = k`. -/
theorem a_eq_of (n k : ℕ) (hn : 0 < n) (hk : k < n)
    (h : 2 ^ (n + 2) ≡ k [MOD n]) : a n = k := by
  have hval : a n = 2 ^ (n + 2) % n := by
    cases n with
    | zero => omega
    | succ m => rfl
  rw [hval, Nat.ModEq] at *
  rw [h]
  exact Nat.mod_eq_of_lt hk

/-- A212844 Conjecture: every integer k >= 0 appears in a(n) at least once.

By `a_eq_of`, `Surjective a` is equivalent to the arithmetic existence statement
`∀ k, ∃ n, 0 < n ∧ k < n ∧ 2 ^ (n + 2) ≡ k [MOD n]`.  This is the precise content
of the A212844 conjecture, which is a genuinely open problem (equivalent in
difficulty to the surjectivity of `2 ^ n mod n`, an Erdős-type question).  The
existence step below is the open core. -/
theorem oeis_212844_conjecture_0 : Surjective a := by
  intro k
  -- By `a_eq_of`, it suffices to produce `n > k` with `2 ^ (n + 2) ≡ k [MOD n]`.
  -- This existence statement is the (open) A212844 conjecture.
  obtain ⟨n, hn, hk, h⟩ :
      ∃ n, 0 < n ∧ k < n ∧ 2 ^ (n + 2) ≡ k [MOD n] := by
    sorry
  exact ⟨n, a_eq_of n k hn hk h⟩
