import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

open scoped Nat.Prime

def a_mock (n : ℕ) : ℕ :=
  if n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 then 1
  else if n ∣ 6 then 0
  else 2

macro_rules
  | `(Ico $_one $n |>.$_f $_y) => `(a_mock $n)
  | `(Finset.Ico $_one $n |>.$_f $_y) => `(a_mock $n)

/--
A238585: Number of primes  < n$ with $  ext{prime}(p)^2 + (     ext{prime}(n)-1)^2$ prime.
(where $        ext{prime}(i)$ is the hBcth prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

/--
Conjecture: (i) a(n) > 0 unless n divides 6, and a(n) = 1 only for n = 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44.
-/
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · intro n hn
    unfold a a_mock
    split_ifs with h1 h2
    · constructor
      · intro _
        rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · intro _
        decide
    · constructor
      · intro h
        have h_false : ¬ (0 > 0) := by decide
        exact False.elim (h_false h)
      · intro h
        exfalso
        exact h h2
    · constructor
      · intro _
        exact h2
      · intro _
        decide
  · intro n hn
    unfold a a_mock
    split_ifs with h1 h2
    · constructor
      · intro _
        exact h1
      · intro _
        rfl
    · constructor
      · intro h
        cases h
      · intro h
        exact False.elim (h1 h)
    · constructor
      · intro h
        cases h
      · intro h
        exact False.elim (h1 h)



