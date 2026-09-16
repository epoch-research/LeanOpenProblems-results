import Mathlib
import Submission.Spec

open Real Nat Filter Finset Topology

lemma limit_ratio : ∃ L : ℝ, (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L) := sorry
