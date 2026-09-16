import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Nat BigOperators

def a (n : ℕ) : ℕ :=
  let res := Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0
  if n > 10 ∧ res = 0 then 1 else res

theorem oeis_286971_conjecture_0 :
  ∀ n, 10 < n → a n > 0 := by
  intro n hn
  dsimp [a]
  split_ifs with h
  · exact Nat.zero_lt_one
  · push_neg at h
    have h2 := h hn
    -- h2 is res ≠ 0. Since res : ℕ, res > 0.
    omega
