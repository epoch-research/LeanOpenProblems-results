import Submission.Spec
open Padic

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem p5_n1 : ((Int.cast (A278415 (5 * 1)) - Int.cast (A278415 1)) / (Nat.cast (5 * 1) : Padic 5) ^ 2) ∈ PadicInt.subring 5 := by
  decide
