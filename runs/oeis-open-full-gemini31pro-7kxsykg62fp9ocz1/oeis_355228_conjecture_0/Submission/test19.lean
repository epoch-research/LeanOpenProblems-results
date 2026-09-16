import Submission.Spec
open Finset Nat Set

def D4_a08 : Finset ℕ := {1, 2, 3, 6}
lemma D4_a08_lcm : D4_a08.lcm id = 6 := by rfl
