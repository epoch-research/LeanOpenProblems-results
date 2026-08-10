import FormalConjectures.Util.ProblemImports

open Nat

def sol_of_nat : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0)
  | 1 => (0, 0, 0, 1)
  | 2 => (0, 0, 1, 1)
  | 3 => (1, 1, 0, 1)
  | _ => (0, 0, 0, 0)

def sol_r : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 4
  | 3 => 3
  | _ => 0

lemma sol_of_nat_correct_bounded_r : ∀ (n : ℕ), n ≤ 3 →
  let s := sol_of_nat n
  s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = n ∧ s.1 ≥ s.2.1 ∧
  (sol_r n)^2 = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  decide

lemma sol_of_nat_correct : ∀ (n : ℕ), n ≤ 3 →
  let s := sol_of_nat n
  s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = n ∧ s.1 ≥ s.2.1 ∧
  (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt * (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  intro n hn
  have h_bounded := sol_of_nat_correct_bounded_r n hn
  generalize h_sol : sol_of_nat n = s
  rw [h_sol] at h_bounded
  rcases h_bounded with ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  have h_sqrt : (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt = sol_r n := by
    rw [← h3]
    exact Nat.sqrt_eq' (sol_r n)
  rw [h_sqrt]
  rw [sq] at h3
  exact h3
