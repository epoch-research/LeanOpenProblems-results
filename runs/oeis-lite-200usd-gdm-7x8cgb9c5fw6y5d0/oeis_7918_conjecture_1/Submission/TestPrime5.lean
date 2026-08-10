import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

lemma a_spec (n : ℕ) : Nat.Prime (a n) ∧ n ≤ a n := by
  unfold a
  exact @Nat.find_spec (fun p : ℕ => Nat.Prime p ∧ n ≤ p) _ _

lemma a_ge_of_no_prime (n q : ℕ) (hn_le_q : n ≤ q) 
    (h_no_prime : ∀ m, n ≤ m → m < q → ¬ Nat.Prime m) : q ≤ a n := by
  have h_spec := a_spec n
  by_contra! hc
  have h1 : n ≤ a n := h_spec.2
  have h2 : a n < q := hc
  have h3 := h_no_prime (a n) h1 h2
  exact h3 h_spec.1
