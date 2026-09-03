import Submission.CofactorMomentSwitching
/-! Exact-type and axiom audit of the cofactor-moment reindexing. -/

open Erdos821.HigherDivisors Erdos821.AnalyticSieve

example (k d X : ℕ) (hd : 0 < d) :
    cofactorMangoldtMoment (k+1) d X =
      ∑ e ∈ Finset.Icc 1 (X/d), (tau k e : ℝ) * residueOneMangoldt (d*e) X :=
  cofactorMangoldtMoment_succ k d X hd

example (r s Q X : ℕ) (hQX : Q ≤ X) :
    (∑ d ∈ Finset.Icc 1 Q, (tau r d : ℝ) * cofactorMangoldtMoment (s+1) d X) =
      ∑ m ∈ Finset.Icc 1 X, truncatedConvolution r s Q m * residueOneMangoldt m X :=
  cofactor_moment_eq_product_moduli r s Q X hQX

example (r s X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, (tau r d : ℝ) * cofactorMangoldtMoment (s+1) d X) =
      shiftedMangoldtMoment (r+s+1) X :=
  full_cofactor_moment_eq_shiftedMoment r s X

example (r s Q X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, truncatedConvolution r s Q m *
      |residueOneMangoldt m X - mangoldtSum X/(m.totient : ℝ)|) ≤
        divisorProgressionError (r+s) X X :=
  product_modulus_error_le_full_discrepancy r s Q X

#print axioms cofactorMangoldtMoment_one
#print axioms cofactor_divisor_filter
#print axioms cofactorMangoldtMoment_succ
#print axioms cofactorMangoldtMoment_nonneg
#print axioms truncated_progressions_le_cofactorMoment
#print axioms sum_convolution_weighted_quotient
#print axioms cofactor_moment_eq_product_moduli
#print axioms truncatedConvolution_nonneg
#print axioms truncatedConvolution_le_tau
#print axioms truncatedConvolution_eq_tau_below
#print axioms full_cofactor_moment_eq_shiftedMoment
#print axioms product_modulus_error_le_full_discrepancy
