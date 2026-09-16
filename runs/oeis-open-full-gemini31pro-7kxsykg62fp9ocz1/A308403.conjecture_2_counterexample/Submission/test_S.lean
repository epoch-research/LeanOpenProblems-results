import Mathlib

noncomputable def A008347_seq : ℕ → ℕ
  | 0 => 0
  | 1 => Nat.nth Nat.Prime 0
  | k + 2 =>
    let p_k_plus_2 := Nat.nth Nat.Prime (k + 1)
    p_k_plus_2 - A008347_seq (k + 1)

-- Cannot #eval because of noncomputable.
