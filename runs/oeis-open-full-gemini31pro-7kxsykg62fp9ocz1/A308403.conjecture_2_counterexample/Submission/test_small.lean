import Mathlib

noncomputable def A008347_seq : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.nth Nat.Prime 0
  | k + 2 =>
    let p_k_plus_2 := Nat.nth Nat.Prime (k + 1)
    p_k_plus_2 - A008347_seq (k + 1)

noncomputable def generalized_a (n base_a base_b : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun i =>
    (Finset.range (n + 1)).sum fun j =>
      if base_a^i + base_b^j < n then
        ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ A008347_seq k = n - (base_a^i + base_b^j))).card
      else
        0

-- We can't evaluate it natively.
