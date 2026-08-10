import FormalConjectures.Util.ProblemImports
example (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : (2 * p + 3) / 3 ≤ n) (hhi : n ≤ p - 1) : n < p := by omega
example : Nat.Prime 5 ∧ 5 ≤ 5 ∧ (2 * 5 + 3)/3 ≤ 4 ∧ 4 ≤ 5 - 1 := by norm_num
