import Submission.InitialCoreDensityReduction

/-! Axiom audit for the cardinality-scale tail and actual core-deficit results. -/
open Erdos970.WeightedMertens Erdos970.GapAverages
#print axioms prime_set_tail_at_budget
#print axioms budgetScaleTail_tendsto_zero
#print axioms filteredDeletionBudget_le_budget_scale
#print axioms filteredDeletionBudget_le_fourth_scale
#print axioms eventually_filteredDeletionBudget_small
#print axioms core_count_le_fourth_deletion_ratio
#print axioms eventually_cover_forces_initial_core_deficit

#print axioms eventually_fourth_bound_of_core_density
#print axioms quadratic_of_critical_initial_core_density
