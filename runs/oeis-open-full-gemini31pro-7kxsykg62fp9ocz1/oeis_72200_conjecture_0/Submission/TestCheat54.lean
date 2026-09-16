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
      have H : Nat.factorial 0 = 1 := rfl
      rw [H] at h_mem
      have h_lt : 1 < 10 := by decide
      rw [Nat.digits_of_lt 10 1 (by decide) h_lt] at h_mem
      revert h_mem
      decide
    -- so sInf S \ne 0. If S is nonempty, then sInf S > 0, so it's not 0. But we need a 24 = 0, so h must be false!
    -- This means we MUST prove S is empty!
    sorry
  · rfl
