import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.factorization_le_iff_dvd
#check Nat.factorization_mul
#check Nat.factorization_pow
#check Nat.factorization_factorial
#check Nat.Prime.multiplicity_factorial
#check Nat.Prime.emultiplicity_factorial
#check padicValNat_factorial
#check Nat.factorization_eq_card_pow_dvd
#check Nat.Prime.pow_dvd_iff_le_factorization
#check Nat.factorization_prod
#check Finset.prod_list_count
#check List.prod_map_dvd_prod_map
#check Int.natAbs_prod
#check Int.natAbs_mul
#check Int.natAbs_sub
#check Nat.factorial_pos
#check Nat.dvd_of_modEq
#check Nat.dvd_mul_left

#check @List.prod_toFinset

#check Int.dvd_iff_dvd_natAbs
#check Int.natAbs_dvd_natAbs
#check Int.dvd_natAbs
#check Int.ofNat_dvd
#check Int.natAbs_ofNat
#check Int.natAbs_mul
#check Int.natAbs_eq_natAbs

#check Nat.add_mul_div_left
#check Nat.mul_add_div
#check Nat.mul_div_right
#check Nat.div_add_mod
#check Nat.mod_add_div
#check Nat.mul_div_mul_left
#check Nat.mul_div_mul_right

#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_of_lt_le
#check Nat.div_eq_iff
#check Nat.div_eq_iff_eq_mul_left
#check Nat.div_eq_of_lt

#check Nat.div_le_of_le_mul
#check Nat.div_lt_of_lt_mul
#check Nat.le_div_iff_mul_le
#check Nat.div_lt_iff_lt_mul

#check Int.natAbs_le
#check Int.natAbs_lt
#check Int.natAbs_of_nonneg
#check Int.natAbs_ofNat
#check Int.ofNat_natAbs_of_nonneg

#check Nat.factorization_eq_zero_of_not_prime
#check Nat.factorization_div
#check Nat.factorization_mul
#check Nat.factorization_factorial
#check Nat.factorization_prod
#check Nat.factorization_le_iff_dvd
#check Nat.factorization_eq_card_pow_dvd
#check Nat.factorization_pow
#check Finsupp.coe_tsub
#check Finsupp.le_def

#check Finset.sum_tsub_distrib
#check Finset.sum_sub_distrib
#check Nat.add_sub_assoc
#check Nat.sub_add_eq
#check tsub_le_iff_right
#check Nat.sub_eq_iff_eq_add
#check Nat.sub_le_sub_left

#check Nat.mul_div_le
#check Nat.lt_succ_mul_self
#check Nat.lt_mul_succ_div
#check Nat.div_lt_iff_lt_mul
#check Nat.mod_lt
#check Nat.div_add_mod

#check Nat.ModEq
#check Nat.modEq_iff_dvd
#check Nat.ModEq.add
#check Nat.ModEq.mul
#check Nat.ModEq.symm
#check Nat.ModEq.trans
#check Nat.mod_modEq
#check Nat.modEq_of_dvd
#check Int.modEq_iff_dvd
#check Int.natCast_dvd_natCast
#check Int.natCast_modEq_natCast

#check Nat.ModEq iff
#check Nat.modEq_iff_modEq
#check Nat.modEq_iff_dvd
#check Nat.modEq_iff_dvd'
#check Nat.modEq_iff_eq_mod
#check Nat.ModEq.iff_eq_mod
#check Nat.ModEq.eq_of_lt_of_lt
#check Nat.ModEq.eq_of_lt_of_lt'

#check Nat.ModEq.refl
#check Nat.ModEq.mul_left'
#check Nat.ModEq.mul_left
#check Nat.ModEq.mul_right
#check Int.natCast_dvd
#check dvd_neg
#check neg_dvd

#check Nat.Prime.eq_two_or_odd
#check Nat.Prime.odd_of_ne_two
#check Nat.Prime.even_iff
#check Odd.pow
#check Even.pow
#check Odd.of_dvd_nat
#check Odd.of_dvd
#check Nat.odd_iff_not_even
#check Nat.even_iff

#check Finset.card_eq_sum_ones
#check Finset.sum_const
#check Finset.sum_congr
#check Finset.card_sigma
#check Finset.sum_sigma
#check Finset.sigma_mk_injective
#check Finset.card_biUnion
#check Finset.card_le_card_of_injOn
