import FormalConjectures.Util.ProblemImports
open Nat
def sol_of_nat : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0)
  | 1 => (0, 0, 0, 1)
  | _ => (0, 0, 0, 0)
lemma sol_correct_0 : let s := sol_of_nat 0; s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = 0 ∧ s.1 ≥ s.2.1 ∧ (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt * (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  unfold sol_of_nat; refine ⟨by decide, by decide, by norm_num⟩
lemma sol_correct_1 : let s := sol_of_nat 1; s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = 1 ∧ s.1 ≥ s.2.1 ∧ (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt * (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  unfold sol_of_nat; refine ⟨by decide, by decide, by norm_num⟩
lemma sol_of_nat_correct : ∀ (n : ℕ), n ≤ 1 →
  let s := sol_of_nat n
  s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = n ∧ s.1 ≥ s.2.1 ∧
  (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt * (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2
  | 0, _ => sol_correct_0
  | 1, _ => sol_correct_1
  | k + 2, h => by omega