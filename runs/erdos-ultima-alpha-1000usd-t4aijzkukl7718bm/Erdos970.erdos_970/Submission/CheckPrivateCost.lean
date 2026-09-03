import Submission.PopulationSignedEntropy
open Erdos970.FiniteGibbs
example (p : ℕ) (ps : List ℕ) (S : Finset ℕ) (t : ℝ) :
    laplaceMoment (count S (p::ps).toFinset) t =
    laplaceMoment (count S (insert p ps.toFinset)) t := by
  rw [List.toFinset_cons]
