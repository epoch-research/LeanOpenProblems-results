import Submission.Lemmas
open Nat Int Finset

lemma d_eq_one (A B n p : ℤ) (h_coprime : Int.gcd A B = 1) (h_np1 : n + 1 = p * p) (hp : ¬ (p ∣ A)) :
  Int.gcd ((n + 1) * A) ((n + 1) * B + A) = 1 := by
  sorry
