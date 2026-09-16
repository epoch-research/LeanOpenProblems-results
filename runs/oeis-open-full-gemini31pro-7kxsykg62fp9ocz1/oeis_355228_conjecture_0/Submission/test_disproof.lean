import Submission.Spec
open Finset Nat Set

theorem disproof_check_type : (type_of% @oeis_355228_conjecture_0) = (∀ n : ℕ, a n > a081512 n ↔ n = 4 ∨ n = 5) := rfl
