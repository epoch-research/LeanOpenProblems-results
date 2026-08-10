import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

theorem primeCounting_succ_le (x : ℕ) : π (x + 1) ≤ π x + 1 := by
  change Nat.primeCounting' (x + 2) ≤ Nat.primeCounting' (x + 1) + 1
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

theorem primeCounting_double_succ_le (x : ℕ) : π (π (x + 1)) ≤ π (π x) + 1 := by
  have h1 : π (x + 1) ≤ π x + 1 := primeCounting_succ_le x
  have h2 : π (π (x + 1)) ≤ π (π x + 1) := Nat.monotone_primeCounting h1
  have h3 : π (π x + 1) ≤ π (π x) + 1 := primeCounting_succ_le (π x)
  exact h2.trans h3

theorem primeCounting_double_add_le (x : ℕ) : ∀ n, π (π (x + n)) ≤ π (π x) + n := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h1 : π (π (x + n + 1)) ≤ π (π (x + n)) + 1 := by
      have h_eq : x + n + 1 = (x + n) + 1 := by omega
      rw [h_eq]
      exact primeCounting_double_succ_le (x + n)
    have h2 : π (π (x + n)) + 1 ≤ π (π x) + n + 1 := by omega
    have h_eq2 : x + (n + 1) = x + n + 1 := by omega
    rw [h_eq2]
    omega

theorem primeCounting_double_step_le (k n : ℕ) : π (π ((k + 1) * n)) ≤ π (π (k * n)) + n := by
  have h_eq : (k + 1) * n = k * n + n := by ring
  rw [h_eq]
  exact primeCounting_double_add_le (k * n) n

theorem primeCounting_double_mono : Monotone (fun x => π (π x)) := by
  intro x y hxy
  exact Nat.monotone_primeCounting (Nat.monotone_primeCounting hxy)
