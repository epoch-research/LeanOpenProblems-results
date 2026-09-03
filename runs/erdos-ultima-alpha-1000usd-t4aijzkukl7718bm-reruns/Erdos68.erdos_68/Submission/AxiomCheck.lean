import Submission.Development

/-! Axiom checks for the main partial results. This is not a solution. -/

#print axioms Erdos68Development.summable_term
#print axioms Erdos68Development.irrational_iff_carry_changes
#print axioms Erdos68Development.termwise_clearing_tail_gt_one
#print axioms Erdos68Development.irrational_sum_powerTerm
#print axioms Erdos68Development.irrational_iff_upperApprox_den_tendsto
#print axioms Erdos68Development.upperApprox_no_return

example : Erdos68Development.carry 3 = (5 : ℤ) := by
  norm_num [Erdos68Development.carry, Erdos68Development.scaledSumQ,
    Finset.sum_range_succ, Nat.factorial]
