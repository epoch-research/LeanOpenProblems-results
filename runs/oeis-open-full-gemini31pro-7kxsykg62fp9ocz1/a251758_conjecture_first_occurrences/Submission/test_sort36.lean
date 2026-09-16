import Mathlib

lemma div_mul {a b : ℕ} (h : a.Coprime b) : Nat.divisors (a * b) = (Nat.divisors a).biUnion (fun d1 => (Nat.divisors b).map ⟨fun d2 => d1 * d2, sorry⟩) := by
  sorry
