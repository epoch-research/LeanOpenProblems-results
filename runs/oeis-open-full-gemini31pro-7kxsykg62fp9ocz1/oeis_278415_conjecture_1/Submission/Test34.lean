import Mathlib
import Submission.Spec

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem test : ((Int.cast (A278415 5) - Int.cast (A278415 1)) / (Nat.cast 5 : Padic 5) ^ 2) ∈ PadicInt.subring 5 := by
  dsimp [PadicInt.subring]
  -- A278415 5 = -24, A278415 1 = 1
  -- diff = -25
  -- den = 25
  -- diff / den = -1
  sorry
