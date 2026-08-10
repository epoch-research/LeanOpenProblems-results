import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

theorem a_eq_self_of_prime (n : ℕ) (hp : Nat.Prime n) : a n = n := by
  dsimp [a]
  rw [Nat.find_eq_iff]
  refine ⟨⟨hp, le_refl _⟩, ?_⟩
  intro m hm
  intro h
  omega
