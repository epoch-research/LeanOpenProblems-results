import Submission.Spec

open Nat

noncomputable def max_A321475 : ℕ := sSup (Set.range A321475)

theorem max_A321475_spec (n : ℕ) : A321475 n ≤ max_A321475 := by
  unfold max_A321475
  apply le_csSup
  · sorry
  · exact Set.mem_range_self n
