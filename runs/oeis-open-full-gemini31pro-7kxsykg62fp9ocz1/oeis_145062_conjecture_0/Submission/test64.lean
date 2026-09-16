import Mathlib

noncomputable def a (n: ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := if z < 1 then 0 else a (z - 1).toNat

macro "try_k" k:term : tactic => `(tactic| {
  use $k
  intro n
  unfold sequence_s_int
  try split_ifs
  all_goals {
    try { rfl }
    try { congr; omega }
    try { omega }
  }
})

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  first
  | try_k 0
  | try_k 1
  | try_k (-1)
  | try_k 2
  | try_k (-2)
