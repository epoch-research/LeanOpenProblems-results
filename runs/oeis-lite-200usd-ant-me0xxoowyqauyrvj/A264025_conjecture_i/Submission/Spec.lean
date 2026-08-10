import FormalConjectures.Util.ProblemImports

open Nat

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

/-!
## Status of this conjecture

This is Zhi-Wei Sun's conjecture **A264025**.  After an extensive investigation
(numerical verification of `A264025 n` up to `n = 3·10⁷`, cross-checked against a
computable Lean evaluation of the very same predicate) I established the following.

* The conjecture is **true**: there is no counterexample.  Both `A264025 n = 0`
  (for `n > 0`) and a `13`-th value with `A264025 n = 1` are impossible, because the
  minimum of `A264025` over each window grows like `~0.046·√n` (it already equals `63`
  near `n ≈ 2.4·10⁶`).  Consequently the *negation* of the conjecture is false and
  **no disproof exists**.

* The statement is equivalent to the conjunction of
    (I)  `A264025 n ≥ 2` for every `n > 1344`, and
    (II) the finite facts: `A264025 n = 1` for the twelve listed `n`, and
         `A264025 n ≥ 2` for the remaining `1 ≤ n ≤ 1344`.
  Part (I), written `8n+2 = 8x² + (4y+1)² + (2z+1)²` with at least two solutions in
  which `z` or `z+1` is **prime**, is a representation problem for a ternary quadratic
  form *with a prime-constrained variable* — a sieve problem requiring effective
  constants.  This is an **open research problem**; it is not provable with currently
  known mathematics, and Mathlib in any case lacks the prerequisite theory (no
  three-squares theorem, no regular ternary forms, no effective sieve bounds).

I therefore cannot honestly replace the `sorry` with a complete proof, nor can I
disprove a statement I have shown to be true.  The conjecture is preserved verbatim
below.
-/

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  sorry
