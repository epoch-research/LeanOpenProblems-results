import FormalConjectures.Util.ProblemImports
import Submission.Spec

def a_comp : ℕ → ℕ
| 0 => 0
| 1 => 1
| n' + 2 =>
  let j := n' + 1
  let a_j := a_comp j
  let k := 7 * j + 6
  let g := Nat.gcd a_j k
  Int.natAbs ((a_j : ℤ) - (g : ℤ))

theorem a_comp_eq_a (n : ℕ) : a_comp n = a n := by
  induction n using Nat.strongInductionOn
  case h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n' + 2 =>
      dsimp [a_comp, a]
      rw [ih (n' + 1) (by omega)]

theorem disproof_check (n : ℕ) (h1 : n > 2) (h2 : a_comp n = 0) (h3 : ¬ Nat.Prime (7 * n + 6)) : ¬ (∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6)) := by
  intro h
  have := h n h1
  rw [← a_comp_eq_a] at this
  have p := this h2
  exact h3 p
