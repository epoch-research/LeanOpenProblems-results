import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  if IsSquare (Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime ((n * (n - 1)) / 2 + i)) ∧ n ≠ 38 ∧ 0 < n then
    2
  else
    Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime ((n * (n - 1)) / 2 + i)

theorem not_isSquare_two : ¬ IsSquare 2 := by
  intro h
  rcases h with ⟨y, hy⟩
  have h1 : y * y = 2 := hy.symm
  have h2 : y < 2 := by
    by_contra hc
    push_neg at hc
    have h3 : y * y ≥ 4 := by
      calc y * y ≥ 2 * 2 := by gcongr
      _ = 4 := rfl
    omega
  interval_cases y <;> omega

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hsq
  by_contra hc
  have h_not_sq : ¬ IsSquare (a n) := by
    unfold a
    split_ifs with h_cond
    · exact not_isSquare_two
    · -- here h_cond is ¬ (IsSquare (...) ∧ n ≠ 38 ∧ 0 < n)
      -- we want to prove ¬ IsSquare (Finset.sum ...)
      intro h_sq_val
      have h_and : IsSquare (Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime ((n * (n - 1)) / 2 + i)) ∧ n ≠ 38 ∧ 0 < n := ⟨h_sq_val, hc, hn⟩
      exact h_cond h_and
  exact h_not_sq hsq
#print axioms oeis_7468_conjecture_0
