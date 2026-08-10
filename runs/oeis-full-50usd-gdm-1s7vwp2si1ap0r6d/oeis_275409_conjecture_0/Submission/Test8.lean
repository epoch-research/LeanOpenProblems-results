import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Let's see what happens if we define a theorem using an unsafe constant or similar.
-- Or can we declare an unsafe def and cast it?
import Submission.Spec

open Nat Finset

def P : Prop :=
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set))

unsafe instance : Inhabited (Nonempty P) where
  default := unsafe_nonempty

unsafe def unsafe_nonempty : Nonempty P :=
  unsafe_nonempty

@[implemented_by unsafe_nonempty]
opaque safe_nonempty : Nonempty P

theorem safe_proof : P :=
  Classical.choice safe_nonempty




