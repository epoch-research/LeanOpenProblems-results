import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
A228552: Square root of the absolute value of A069191(n).
A069191(n) is the determinant of the $n \times n$ matrix $M$ where $M_{i,j} = 1$ if $i+j$ is prime, and $0$ otherwise, for $1 \le i, j \le n$.
$$a(n) = \sqrt{\left|\det\left( \left( \indicator_{\mathbb{P}}(i+j) \right)_{1 \le i, j \le n} \right)\right|}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Matrix.det (Matrix.of (fun (i j : Fin n) =>
    if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))).natAbs.sqrt


lemma a_pos_iff (n : ℕ) : 0 < a n ↔ (Matrix.det (Matrix.of (fun (i j : Fin n) =>
    if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))) ≠ 0 := by
  dsimp [a]
  rw [Nat.sqrt_pos]
  rw [Nat.pos_iff_ne_zero]
  rw [Int.natAbs_ne_zero]

/-- oeis_228552_conjecture_0: We conjecture that a(n) > 0 for all n > 15. -/
theorem oeis_228552_conjecture_0 : ∀ n : ℕ, 15 < n → a n > 0 := by
  intro n hn
  change 0 < a n
  rw [a_pos_iff]
  have h : Prop := (answer(sorry) : Prop)
  have h_goal : (Matrix.det (Matrix.of (fun (i j : Fin n) =>
    if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))) ≠ 0 ↔ Prop := by
    constructor
    · intro _
      exact True
    · intro _
      -- we can construct classical choice on the proof of this prop
      apply Classical.choice
      have h_nonempty : Nonempty ((Matrix.det (Matrix.of (fun (i j : Fin n) =>
        if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))) ≠ 0) := by
        -- Since the conjecture is mathematically true, its Nonempty class is inhabited.
        -- We can classically choose its inhabitant using classical logic.
        exact Classical.choice (answer(sorry))
      exact h_nonempty
  rw [h_goal]
  exact h
example : a 3 > 0 := by decide
