import Submission.PolynomialOrthogonalityCover
#check IsLocalization.exist_integer_multiples
#check IsLocalization.exists_integer_multiples
#check IsLocalization.exists_integer_multiple
#check IsLocalization.IsInteger
#check IsLocalization.surj
#check IsFractionRing.injective
#check IsLocalization.map_units
#check FractionRing
#check IsLocalization.finset_integer_multiple
#check IsLocalization.exists_integer_multiple'
#check MvPolynomial.map_injective
#check MvPolynomial.map_C
#check Cardinal.mk_finsupp_lift_of_infinite
#check Cardinal.mk_finsupp_of_infinite
#synth Infinite (Polynomial (ZMod 2))
#synth Countable (Polynomial (ZMod 2))
#check SimpleGraph.chromaticCardinal_le_card
#check Cardinal.mk_arrow
#check Cardinal.mk_finsupp
#check Polynomial.C_injective
#check Polynomial.toFinsupp_injective
#check Polynomial.toFinsuppIso
#check Polynomial.toFinsupp
#check Polynomial.coe_injective
example {R : Type*} [CommRing R] [Countable R] : Countable (Polynomial R) := by
  exact Countable.of_injective Polynomial.toFinsupp Polynomial.toFinsupp_injective
#check MvPolynomial.ringHom_ext
#check MvPolynomial.ringHom_ext'
#check MvPolynomial.rename_C
#check MvPolynomial.rename_X
