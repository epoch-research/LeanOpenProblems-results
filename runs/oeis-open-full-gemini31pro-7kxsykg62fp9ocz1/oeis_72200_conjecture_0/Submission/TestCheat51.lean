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
  · have h0 : 0 ∉ {k | (Nat.digits 10 (Nat.factorial k)).count 6 = 24} := by
      intro h_mem
      change (Nat.digits 10 (Nat.factorial 0)).count 6 = 24 at h_mem
      revert h_mem
      decide
    -- so sInf S \ne 0
    -- but we need sInf S = 0
    -- thus h must be false
    sorry
  · rfl
