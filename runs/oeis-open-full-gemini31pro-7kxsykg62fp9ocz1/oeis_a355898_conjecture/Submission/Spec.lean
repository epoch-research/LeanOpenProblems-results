import FormalConjectures.Util.ProblemImports
import Submission.Proof5

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) :=
by sorry

theorem oeis_a355898_conjecture.disproof : ¬ (type_of% @oeis_a355898_conjecture) := by
  intro h_all
  have h_conj_copy : ∀ n ≥ 3775, A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2) := by
    intro n hn
    have h_conj := h_all n hn
    have hc : A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) := h_conj.1
    have heq : A355898 = A355898_copy := by
      apply funext
      intro m
      induction m using Nat.strong_induction_on with
      | h k ih =>
        cases k with
        | zero => rfl
        | succ m =>
          cases m with
          | zero => rfl
          | succ j =>
            cases j with
            | zero => rfl
            | succ i =>
              have ih1 := ih (i + 2) (by omega)
              have ih2 := ih (i + 1) (by omega)
              change Nat.gcd (A355898 (i + 2)) (A355898 (i + 1)) + (A355898 (i + 2) + A355898 (i + 1)) / Nat.gcd (A355898 (i + 2)) (A355898 (i + 1)) = _
              rw [ih1, ih2]
              rfl
    rw [← heq]
    exact hc
  exact A355898_copy_contradiction h_conj_copy
