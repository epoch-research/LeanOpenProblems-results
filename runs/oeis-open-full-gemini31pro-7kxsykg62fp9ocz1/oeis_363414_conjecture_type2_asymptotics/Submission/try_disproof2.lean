import Submission.Spec
import Mathlib

open Filter Asymptotics

theorem disproof_test : ¬ (type_of% @oeis_363414_conjecture_type2_asymptotics) := by
  intro h
  have h5 : Nat.Prime 5 := by norm_num
  have h5_type2 : 5 ∈ type_two_primes_conjectured := by
    dsimp [type_two_primes_conjectured]
    constructor
    · norm_num
    · rfl
  have h_asymp := h 5 h5 h5_type2
  sorry
