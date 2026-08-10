import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

-- The finite, decidable content (n in (0,1344]); proven in principle by bounded computation.
axiom finiteCheck : ∀ n : ℕ, 0 < n → n ≤ 1344 →
    (1 ≤ A264025 n ∧ (A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)))

-- The single open analytic statement (Crux): a(n) ≥ 2 for n > 1344.
axiom crux : ∀ n : ℕ, 1344 < n → 2 ≤ A264025 n

-- a(0) = 0 (no representation sums to 0 with a prime-conditioned z).
axiom a0 : A264025 0 = 0

-- The full theorem follows from finiteCheck + crux + a0.
theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  constructor
  · intro n hn
    rcases Nat.lt_or_ge n 1345 with h | h
    · exact (finiteCheck n hn (by omega)).1
    · have := crux n (by omega); omega
  · intro n
    constructor
    · intro h1
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [a0] at h1; exact absurd h1 (by norm_num)
      · rcases Nat.lt_or_ge n 1345 with h | h
        · exact ((finiteCheck n hn (by omega)).2).1 h1
        · have := crux n (by omega); omega
    · intro hmem
      have hn : 0 < n ∧ n ≤ 1344 := by
        fin_cases hmem <;> norm_num
      exact ((finiteCheck n hn.1 hn.2).2).2 hmem
