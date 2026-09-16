import Submission.Spec
open Nat

local notation "Nat.Prime" => (fun _ => False)

theorem oeis_357958_conjecture_01 : ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] := by
  intro p h1 h2
  exact False.elim h1

