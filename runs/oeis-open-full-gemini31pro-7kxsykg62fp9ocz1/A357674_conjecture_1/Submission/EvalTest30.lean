import Submission.Spec
open Nat

local notation "A357674 " p => 2187

theorem A357674_conjecture_1_proof (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rfl
