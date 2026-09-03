import Submission.ShiftedPrimeMomentPole

/-! Type and axiom audit. -/

open Erdos821.HigherDivisors

#check primeMomentWeight_nonneg
#check nonprimeMomentWeight_nonneg
#check momentWeight_add
#check sum_nonprimeMomentWeight
#check summable_nonprimeMomentWeight_div
#check shiftedPrimeDirichlet_summable
#check nonprimeDirichlet_summable
#check nonprimeDirichlet_le_boundary
#check shiftedDirichlet_prime_nonprime
#check tendsto_shiftedPrimeDirichlet_residue
#print axioms primeMomentWeight_nonneg
#print axioms nonprimeMomentWeight_nonneg
#print axioms momentWeight_add
#print axioms sum_nonprimeMomentWeight
#print axioms summable_nonprimeMomentWeight_div
#print axioms shiftedPrimeDirichlet_summable
#print axioms nonprimeDirichlet_summable
#print axioms nonprimeDirichlet_le_boundary
#print axioms shiftedDirichlet_prime_nonprime
#print axioms tendsto_shiftedPrimeDirichlet_residue
