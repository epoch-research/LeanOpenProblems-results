import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

theorem a_two : a 2 = 2 := by
  dsimp [a]
  have h2 : Nat.Prime 2 ∧ 2 ≤ 2 := ⟨Nat.prime_two, le_refl _⟩
  have h_find := Nat.find_le h2
  have h_min := Nat.find_min' (by
    rcases Nat.exists_infinite_primes 2 with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  ) h2
  -- Wait, let's see what we can do with h_find and Nat.find_spec
  sorry
