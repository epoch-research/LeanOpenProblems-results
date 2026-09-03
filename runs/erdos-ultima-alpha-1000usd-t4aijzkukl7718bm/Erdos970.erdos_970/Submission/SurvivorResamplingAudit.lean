import Submission.PrimeCoverResampling
import Submission.ConditionalSurvivorChernoff

/-! Axiom audit for the resampling and conditional variance branch.
None of these auxiliary results proves or disproves erdos_970. -/
#print axioms Erdos970.Resampling.prime_resampling_increment
#print axioms Erdos970.Resampling.prime_increment_second_moment
#print axioms Erdos970.Resampling.prime_covered_second_moment
#print axioms Erdos970.Resampling.no_survivor_only_conditional_second_moment
#print axioms Erdos970.GapAverages.progression_distribution
#print axioms Erdos970.GapAverages.mean_rowConditionalVariance_rounded
#print axioms Erdos970.GapAverages.mean_rowConditionalVariance_le
#print axioms Erdos970.Resampling.phaseMean_exp_centered_sum_le
#print axioms Erdos970.Resampling.populationCoveredFraction_le
#print axioms Erdos970.Resampling.mean_classVariance_sum
