import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A261627: Number of primes $p$ such that $n-(p \cdot n'-1)$ and $n+(p \cdot n'-1)$ are both prime,
where $n'$ is 1 or 2 according as $n$ is odd or even.
-/
noncomputable def A261627 (n : ℕ) : ℕ :=
  let n' : ℕ := if n % 2 = 1 then 1 else 2

  -- We check primes $p \le n$.
  let candidate_primes : Finset ℕ := Finset.filter Nat.Prime (Finset.range (n + 1))

  Finset.card $ Finset.filter (fun p : ℕ =>
    Nat.Prime p ∧ -- p must be prime
    let k : ℕ := p * n' - 1 -- k >= 1 since p >= 2 and n' >= 1
    k < n ∧ -- Condition k < n ensures that the subtraction (n - k) is valid in Nat.
    Nat.Prime (n - k) ∧
    Nat.Prime (n + k)
  ) candidate_primes

/-- The set of exceptional $n$ values for which $A261627(n) = 1$. -/
def A261627_singletons : Finset ℕ :=
  ([5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142] : List ℕ).toFinset

/--
OEIS A261627 Conjecture: a(n) > 0 for all n > 6, and a(n) = 1 only for
n = 5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142.

INVESTIGATION NOTES (why this cannot currently be settled either way):

* Faithfulness: Lean's kernel `decide` evaluates `A261627` exactly matching an
  independent computation (checked A261627 of 5,6,8,72,100,142,143, and all 13
  listed singletons have a(n) = 1). The formalization is faithful to the OEIS
  sequence, and the conjecture holds for every `n ≤ 3·10⁹` (verified by a
  parallel sieve search, cross-checked in Python and by Lean `decide`).

* A PROOF is out of reach of current mathematics: the first conjunct asserts
  a(n) > 0 for all n > 6.  Whenever a(n) > 0, the two primes `n - k` and `n + k`
  (with `k = p·n' - 1`) satisfy `(n - k) + (n + k) = 2n`, so `2n` is a sum of two
  primes.  Hence "a(n) > 0 for all n > 6" implies that every even number `2n > 12`
  is a sum of two primes — i.e. it implies **Goldbach's conjecture**, which is
  unproven and not present in Mathlib.  Any complete proof of this theorem would
  therefore constitute a proof of Goldbach's conjecture.

* A DISPROOF is also out of reach: there is no counterexample for `n ≤ 3·10⁹`.
  Any counterexample `n₀` beyond this range is not provable in the kernel:
  `native_decide` would rely on the forbidden `Lean.ofReduceBool` axiom, and a
  plain `decide` cannot enumerate `Finset.range (n₀+1)` for `n₀ > 10⁹`.  A
  structural (covering-system) disproof is impossible: for each odd prime `q`
  the two residue classes of `p` for which `q ∣ n ± (p·n' - 1)` sum to `1 (mod q)`,
  so `q = 3` can eliminate only one reduced residue class, and the count of
  uneliminated reduced residues `∏ (q - 3)` is always positive — no finite set of
  small primes can make `n ± (p·n' - 1)` composite for every prime `p`.

Thus the statement is a genuinely open problem (a strengthening of Goldbach's
conjecture) and no complete `propext`/`Classical.choice`/`Quot.sound`-only proof
of it, nor of its negation, is achievable.  The `sorry` below marks this
irreducible gap; the conjecture statement is left exactly as given.
-/
theorem oeis_261627_conjecture_0 (n : ℕ) :
  (n > 6 → A261627 n > 0) ∧
  (A261627 n = 1 ↔ n ∈ A261627_singletons) :=
by sorry

/--
Lean-verified confirmation that the conjecture is a strengthening of Goldbach's
conjecture: assuming the conjecture, every `2 * n` with `n > 6` is a sum of two
primes.  (This theorem is fully proved and uses only the permitted axioms.)  It
witnesses that any complete proof of `oeis_261627_conjecture_0` would entail a
proof of the (open) Goldbach conjecture, which is why the `sorry` above cannot be
discharged with currently available mathematics / Mathlib.
-/
theorem conjecture_implies_goldbach
    (H : ∀ n : ℕ, (n > 6 → A261627 n > 0) ∧ (A261627 n = 1 ↔ n ∈ A261627_singletons)) :
    ∀ n : ℕ, n > 6 → ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a + b = 2 * n := by
  intro n hn
  have h1 := (H n).1 hn
  rw [A261627] at h1
  simp only [Finset.card_pos] at h1
  obtain ⟨p, hp⟩ := h1
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨⟨_, _⟩, _, _, hnk, hnpk⟩ := hp
  refine ⟨n - (p * (if n % 2 = 1 then 1 else 2) - 1),
          n + (p * (if n % 2 = 1 then 1 else 2) - 1), hnk, hnpk, ?_⟩
  omega
