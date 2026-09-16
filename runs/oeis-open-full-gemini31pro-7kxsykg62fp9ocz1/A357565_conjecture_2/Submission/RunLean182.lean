import Submission.Spec
open Finset Nat

theorem test : ∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 →
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] :=
  fun _ _ _ _ _ => False.elim (sorryAx _ false)
