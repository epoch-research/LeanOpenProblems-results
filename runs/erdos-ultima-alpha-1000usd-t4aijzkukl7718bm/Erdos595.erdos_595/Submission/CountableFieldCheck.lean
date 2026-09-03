import FormalConjecturesUtil
open scoped TensorProduct
variable (F : Type*) [Field F] [Countable F]
#synth Countable (MvPolynomial ℕ F)
#synth Countable (FractionRing (MvPolynomial ℕ F))
#synth Countable (AlgebraicClosure F)
#check Cardinal.mk_le_aleph0_iff
#check Module.IsTorsionFree.of_algebraMap_injective
#check NoZeroSMulDivisors.iff_algebraMap_injective
#check AlgebraicIndependent.map
#check AlgebraicIndependent.map'
#check AlgebraicIndependent.comp
#check AlgebraicIndependent.restrictScalars
#check AlgebraicIndependent.aevalEquiv_apply_coe
