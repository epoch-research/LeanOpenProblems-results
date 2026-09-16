import Mathlib
import Submission.Spec

open Nat Finset

def f (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d * (Nat.divisors d).card

lemma f_pm {p m : ℕ} (hp : p.Prime) (h_coprime : p.Coprime m) (hm : 0 < m) :
  f (p * m) = f m + p * ∑ d ∈ m.divisors, d * (Nat.divisors (p * d)).card := by
  have hd : (p * m).divisors = m.divisors ∪ m.divisors.map ⟨fun d => p * d, fun _ _ h => mul_left_cancel₀ hp.pos.ne.symm h⟩ := by
    sorry
  sorry
