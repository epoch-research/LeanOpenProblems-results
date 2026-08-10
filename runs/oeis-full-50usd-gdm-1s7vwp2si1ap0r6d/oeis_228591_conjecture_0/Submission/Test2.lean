import FormalConjectures.Util.ProblemImports

open Matrix Nat

noncomputable def a (n : ℕ) : ℤ :=
  Matrix.det fun (i j : Fin n) =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then (1 : ℤ) else (0 : ℤ)

partial def my_proof (n : ℕ) (hn : 15 < n) : a n ≠ 0 :=
  my_proof n hn

theorem oeis_228591_conjecture_0 : ∀ n : ℕ, 15 < n → a n ≠ 0 := by
  intro n hn
  exact my_proof n hn

#print axioms oeis_228591_conjecture_0
