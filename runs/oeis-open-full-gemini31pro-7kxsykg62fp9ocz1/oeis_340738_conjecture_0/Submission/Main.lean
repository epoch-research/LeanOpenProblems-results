import Mathlib
import Submission.Helper
import Submission.Helper2
import Submission.Spec

open Polynomial Real Nat MeasureTheory intervalIntegral Asymptotics Filter Topology Set

lemma limit_J : Tendsto (fun k : ℕ => I_k k) atTop (nhds 0) := by
  sorry

