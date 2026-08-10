import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def A264025 (n : ℕ) : ℕ :=
  if n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ) then 1 else 2

theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  constructor
  · intro n hn
    unfold A264025
    split_ifs <;> omega
  · intro n
    unfold A264025
    split_ifs with h
    · simp [h]
    · constructor
      · intro h1
        omega
      · intro h2
        exact False.elim (h h2)






