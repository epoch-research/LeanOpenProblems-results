import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

-- try to prove next_prime 2 = 3
theorem test1 : next_prime 2 = 3 := by
  unfold next_prime
  apply le_antisymm
  · apply csInf_le
    · exact Nat.bddBelow_def.mpr (fun _ _ => Nat.zero_le _)
    · simp [Nat.prime_three]
  · apply le_csInf
    · exact ⟨3, by simp [Nat.prime_three]⟩
    · intro b hb
      simp at hb
      have : 2 < b := hb.2
      have : 3 ≤ b ∨ b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases this with h | h | h | h
      · exact h
      · subst h; exact absurd hb.1 Nat.not_prime_zero
      · subst h; exact absurd hb.1 Nat.not_prime_one
      · omega
