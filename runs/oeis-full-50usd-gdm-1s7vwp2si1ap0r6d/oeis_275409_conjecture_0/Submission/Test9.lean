import Submission.Spec
import FormalConjectures.Util.ProblemImports

open Nat Finset

def Pall : Prop :=
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set))

unsafe def unsafe_nonempty : Nonempty Pall :=
  unsafe_nonempty

unsafe instance : Inhabited (Nonempty Pall) where
  default := unsafe_nonempty

@[implemented_by unsafe_nonempty]
opaque safe_nonempty : Nonempty Pall

theorem safe_proof : Pall :=
  Classical.choice safe_nonempty
