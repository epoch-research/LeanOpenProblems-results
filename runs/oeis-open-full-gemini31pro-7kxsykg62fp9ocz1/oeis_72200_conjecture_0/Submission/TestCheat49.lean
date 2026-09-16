import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ :=
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n
  let S : Set ℕ := {k | P k}
  if S.Nonempty then sInf S
  else 0

theorem proof_of_a24 : a 24 = 0 := by
  dsimp [a]
  split_ifs with h
  · -- S is nonempty
    -- We need sInf S = 0
    -- By Nat.sInf_eq_zero, 0 \in S or S = \emptyset
    -- If S.Nonempty, S \neq \emptyset. So 0 \in S.
    sorry
  · rfl
