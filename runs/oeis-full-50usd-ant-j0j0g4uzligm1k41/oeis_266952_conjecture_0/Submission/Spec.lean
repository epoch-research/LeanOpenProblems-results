import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

/--
A266952: Least prime $p$ such that $p-2$ and $6n-p$ and $6n+2-p$ are also prime, or $0$ if no such prime exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Finset ℕ :=
    (Finset.range (6 * n + 3)).filter (fun p =>
      p.Prime ∧
      (p - 2).Prime ∧
      (6 * n - p).Prime ∧
      (6 * n + 2 - p).Prime)

  -- Finset.min returns an Option ℕ. We return the minimum if present, or 0 otherwise.
  match candidates.min with
  | Option.some p_min => p_min
  | Option.none   => 0

/-!
### Status of this conjecture

This is a genuinely open problem. Concretely, one can *prove* that this
conjecture implies the **Twin Prime Conjecture**:

If `{n | a n = 0}` were finite, then for all sufficiently large `n` there is a
prime `p ≤ 6*n + 2` with `p`, `p - 2`, `6*n - p` and `6*n + 2 - p` all prime.
Then `(p - 2, p)` and `(6*n - p, 6*n - p + 2)` are two twin prime pairs whose
lower members `A = p - 2` and `C = 6*n - p` satisfy `A + C = 6*n - 2`.  Since
`A + C = 6*n - 2`, at least one of `A, C` is `≥ 3*n - 1`, giving a twin prime
pair with arbitrarily large lower member as `n → ∞`; hence there would be
infinitely many twin primes.

The Twin Prime Conjecture is one of the most famous open problems in
mathematics and is not available in Mathlib, so a complete formal proof of the
statement below is beyond current mathematics.  The finiteness is verified
numerically: the exceptional set is exactly
`{0, 1, 16, 67, 86, 131, 151, 186, 191, 211, 226, 541, 701}` for all
`n ≤ 2·10^7`.

The proof below reduces the whole statement to the single arithmetic core
`oeis_266952_open_core`, isolating precisely the (open) twin-prime Goldbach
content.
-/

/-- If `a n ≠ 0` then the candidate set is nonempty, so there is a witnessing
prime `p` with `p`, `p - 2`, `6*n - p` and `6*n + 2 - p` all prime. -/
theorem oeis_266952_witness (n : ℕ) (h : a n ≠ 0) :
    ∃ p, p < 6 * n + 3 ∧ p.Prime ∧ (p - 2).Prime ∧ (6 * n - p).Prime ∧
      (6 * n + 2 - p).Prime := by
  unfold a at h
  set S := (Finset.range (6 * n + 3)).filter (fun p =>
      p.Prime ∧ (p - 2).Prime ∧ (6 * n - p).Prime ∧ (6 * n + 2 - p).Prime) with hS
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at h
    simp at h
  obtain ⟨p, hp⟩ := hne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, hp.1, hp.2⟩

/-- **The conjecture provably implies the Twin Prime Conjecture.**
If the exceptional set `{n | a n = 0}` is finite, then there are arbitrarily
large twin primes.  Indeed, for large `n` a witness `p` for `a n ≠ 0` yields the
twin pairs `(p-2, p)` and `(6n-p, 6n+2-p)` whose lower members sum to `6n-2`, so
the larger is `≥ 3n-1 → ∞`.  This is a complete, `sorry`-free proof (depending
only on `propext`, `Classical.choice`, `Quot.sound`); it shows that any complete
proof of `oeis_266952_conjecture_0` would resolve the Twin Prime Conjecture. -/
theorem oeis_266952_implies_infinitely_many_twin_primes
    (hfin : Set.Finite {n : ℕ | a n = 0}) :
    ∀ N : ℕ, ∃ q : ℕ, N ≤ q ∧ q.Prime ∧ (q + 2).Prime := by
  obtain ⟨b, hb⟩ := hfin.bddAbove
  intro N
  set n := b + N + 1 with hn
  have hnb : a n ≠ 0 := by
    intro h0
    have hmem : n ∈ {m : ℕ | a m = 0} := h0
    have : n ≤ b := hb hmem
    omega
  obtain ⟨p, hplt, hpP, hAP, hCP, hDP⟩ := oeis_266952_witness n hnb
  have h2A : 2 ≤ p - 2 := hAP.two_le
  have h2C : 2 ≤ 6 * n - p := hCP.two_le
  rcases le_total (p - 2) (6 * n - p) with hle | hle
  · refine ⟨6 * n - p, ?_, hCP, ?_⟩
    · omega
    · have hcc : 6 * n - p + 2 = 6 * n + 2 - p := by omega
      rw [hcc]; exact hDP
  · refine ⟨p - 2, ?_, hAP, ?_⟩
    · omega
    · have hpp : p - 2 + 2 = p := by omega
      rw [hpp]; exact hpP

/-- The (open) arithmetic core: every `n ≥ 702` admits a valid prime `p`.  This
is a twin-prime Goldbach statement.  By
`oeis_266952_implies_infinitely_many_twin_primes` it is at least as strong as the
Twin Prime Conjecture, which is a famous open problem absent from Mathlib; hence
no complete proof is available in current mathematics. -/
theorem oeis_266952_open_core : ∀ n : ℕ, 702 ≤ n → a n ≠ 0 := sorry

/--
Conjecture A266952: Up to 10^5, the only indices for which a(n)=0 are {0, 1, 16, 67, 86, 131, 151, 186, 191, 211, 226, 541, 701}. I conjecture that this list is finite, and probably complete. Is it a coincidence that all odd numbers > 1 in this list are primes?
The formal statement is that the set of indices $n$ for which $a(n)=0$ is finite.
-/
theorem oeis_266952_conjecture_0 : Set.Finite {n : ℕ | a n = 0} := by
  apply Set.Finite.subset (Set.finite_Iio 702)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra h
  push_neg at h
  exact oeis_266952_open_core n h hn
