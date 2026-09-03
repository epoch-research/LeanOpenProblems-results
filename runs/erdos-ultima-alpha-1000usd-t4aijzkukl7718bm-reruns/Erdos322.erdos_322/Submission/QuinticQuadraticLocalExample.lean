import FormalConjecturesUtil

/-! Explicit local quadratic identities. These are not rational identities
and do not prove any representation-count bound. -/
namespace Erdos322Research.QuinticQuadraticLocalExample

open Polynomial

/-- A polynomial identity modulo eleven, rather than just a finite collection
of evaluations. -/
theorem identity_mod_eleven :
    (X : (ZMod 11)[X]) ^ 5 + (X ^ 2) ^ 5 +
      (X ^ 2 + 7 * X + 2) ^ 5 + (2 * X ^ 2 + 5 * X + 1) ^ 5 +
      (7 * X ^ 2 + 4 * X + 1) ^ 5 = 1 := by
  have hz : (11 : (ZMod 11)[X]) = 0 := CharP.cast_eq_zero _ 11
  linear_combination (norm := ring)
    (3 +
      55 * X +
      405 * X ^ 2 +
      1590 * X ^ 3 +
      3615 * X ^ 4 +
      5087 * X ^ 5 +
      5475 * X ^ 6 +
      6210 * X ^ 7 +
      6315 * X ^ 8 +
      4405 * X ^ 9 +
      1531 * X ^ 10) * hz

/-- An exact first lift of the preceding identity, with the constant target
still equal to one. This is not an identity over the rationals. -/
theorem identity_mod_one_twenty_one :
    (77 * (X : (ZMod 121)[X]) ^ 2 + X + 110) ^ 5 +
      (78 * X ^ 2 + 77 * X + 66) ^ 5 +
      (111 * X ^ 2 + 84 * X + 79) ^ 5 +
      (46 * X ^ 2 + 5 * X + 45) ^ 5 +
      (7 * X ^ 2 + 4 * X + 1) ^ 5 = 1 := by
  have hz : (121 : (ZMod 121)[X]) = 0 := CharP.cast_eq_zero _ 121
  linear_combination (norm := ring)
    (170405100 +
      202470025 * X +
      1142140470 * X ^ 2 +
      1535741610 * X ^ 3 +
      3285307725 * X ^ 4 +
      3435024811 * X ^ 5 +
      3984569045 * X ^ 6 +
      2743744850 * X ^ 7 +
      1794921880 * X ^ 8 +
      647086805 * X ^ 9 +
      187194379 * X ^ 10) * hz

end Erdos322Research.QuinticQuadraticLocalExample
