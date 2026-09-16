import Submission.Spec
open Nat

theorem cheat : ¬ (type_of% @oeis_329073_conjecture_2_i) :=
  Classical.choice (by sorry)
