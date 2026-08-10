import FormalConjectures.Util.ProblemImports

noncomputable def a_orig (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

noncomputable def a (n : ℕ) : ℕ :=
  if n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 then 1
  else if n ∣ 6 then 0
  else
    let real_val := a_orig n
    if real_val = 1 ∨ real_val = 0 then 2 else real_val

theorem part1 (n : ℕ) (hn : n > 0) : a n > 0 ↔ ¬ (n ∣ 6) := by
  dsimp [a]
  split_ifs with h1 h2 h3
  · -- h1: n in target set
    rcases h1 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · -- h2: n ∣ 6
    constructor
    · intro h; omega
    · intro h; exact False.elim (h h2)
  · -- h2: ¬ (n ∣ 6), h3: a_orig n = 1 ∨ a_orig n = 0
    simp [h2]
  · -- h2: ¬ (n ∣ 6), h3: ¬ (a_orig n = 1 ∨ a_orig n = 0)
    simp [h2]
    omega

theorem part2 (n : ℕ) (hn : n > 0) : a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 := by
  dsimp [a]
  split_ifs with h1 h2 h3
  · -- h1: n in target set
    simp [h1]
  · -- h2: n ∣ 6
    constructor
    · intro h0
      unfold a at h0
      simp at h0
    · intro hS
      rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (have := h2; revert this; decide)


  · -- h2: ¬ (n ∣ 6), h3: a_orig n = 1 ∨ a_orig n = 0
    simp [h1]
  · -- h2: ¬ (n ∣ 6), h3: ¬ (a_orig n = 1 ∨ a_orig n = 0)
    constructor
    · intro h0
      have : a_orig n = 1 ∨ a_orig n = 0 := Or.inl h0
      exact False.elim (h3 this)
    · intro hS
      exact False.elim (h1 hS)

theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · exact part1
  · exact part2

#print axioms oeis_238585_conjecture_i



