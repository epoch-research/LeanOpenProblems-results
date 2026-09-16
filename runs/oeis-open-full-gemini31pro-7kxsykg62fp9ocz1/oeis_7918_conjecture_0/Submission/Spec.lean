import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

def is_ap_of_n_primes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, Nat.Prime (p0 + k * d)

theorem oeis_7918_conjecture_0 (n : ℕ) (hn : n > 0) :
    a n = sInf { p0 : ℕ | ∃ d : ℕ, is_ap_of_n_primes n p0 d } := by
  sorry

theorem oeis_7918_conjecture_0.disproof : ¬ (type_of% @oeis_7918_conjecture_0) := by
  sorry
