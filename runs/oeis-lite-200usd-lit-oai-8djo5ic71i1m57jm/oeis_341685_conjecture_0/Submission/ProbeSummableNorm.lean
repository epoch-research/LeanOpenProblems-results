import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Filter Topology

#check Summable.norm
#check Summable.nnnorm
#check summable_norm_iff
#check summable_norm_iff_of_nonarchimedean
#check Summable.hasSum
#check summable_iff_vanishing_norm

example : ¬ Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  intro hs
  have hnorm := hs.norm
  -- maybe contradiction if ‖factorial‖ as real not summable? but p-adic norm is small, likely summable.
  sorry
