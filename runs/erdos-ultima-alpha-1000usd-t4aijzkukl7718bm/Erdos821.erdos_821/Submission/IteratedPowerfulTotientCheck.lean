import Submission.IteratedPowerfulTotient

/-! Type and axiom audit for the iterated high-power injectivity results. -/

open Erdos821.IteratedTotient

#check factorization_totient
#check factorization_eq_or_le_of_iterate_eq
#check eq_of_iterate_eq_of_low_exponent_agreement
#check lowExponentSignature_injOn_fiber
#check iterate_injective_on_highPower
#check iterate_pow_injective
#check highPower_fiber_card_le_one
#print axioms factorization_totient
#print axioms factorization_eq_or_le_of_iterate_eq
#print axioms eq_of_iterate_eq_of_low_exponent_agreement
#print axioms lowExponentSignature_injOn_fiber
#print axioms iterate_injective_on_highPower
#print axioms iterate_pow_injective
#print axioms highPower_fiber_card_le_one
