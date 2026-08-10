import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check padicNorm
#check padicNorm.of_int
#check padicNorm.of_nat
#check padicNorm.of_rat
#check padicNorm.toNNReal
#check norm_num
#check padicNorm_e.of_int
#check padicNormE
#check padicValNat_factorial
#check padicValNat_factorial_le
#check sub_one_mul_padicValNat_factorial
#check Padic.norm_eq
#check Padic.norm_eq_zpow_neg_valuation
#check Padic.norm_p_pow
#check norm_num1
