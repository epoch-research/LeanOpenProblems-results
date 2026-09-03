import Submission.DiagonalBound

/-!
# Verification of the diagonal bound

The printed axiom sets should contain only the usual Lean/mathlib axioms:
`propext`, `Classical.choice`, and `Quot.sound`. In particular there must be no
`sorryAx` or compiler-trust axiom. The examples exercise the claimed bound,
its necessary-condition corollary, and a wrapped negative-coordinate edge.
-/

#check @Erdos952.DiagonalBound.certificate
#check @Erdos952.no_bounded_step_sequence_of_bound_le_four
#check @Erdos952.five_le_bound_of_witness

#print axioms Erdos952.DiagonalBound.mem_exceptionBox_of_norm_le
#print axioms Erdos952.DiagonalBound.finite_exceptions
#print axioms Erdos952.DiagonalBound.norm_eq_of_prime_dvd
#print axioms Erdos952.DiagonalBound.twoSubI_dvd_of_congruence
#print axioms Erdos952.DiagonalBound.twoAddI_dvd_of_congruence
#print axioms Erdos952.DiagonalBound.threeAddTwoI_dvd_of_congruence
#print axioms Erdos952.DiagonalBound.threeSubTwoI_dvd_of_congruence
#print axioms Erdos952.DiagonalBound.prime_congruences
#print axioms Erdos952.DiagonalBound.prime_odd
#print axioms Erdos952.DiagonalBound.even_sub_of_odd
#print axioms Erdos952.DiagonalBound.zero_or_diagonal_of_even_of_norm_lt_four
#print axioms Erdos952.DiagonalBound.norm_ne_three
#print axioms Erdos952.DiagonalBound.certificate
#print axioms Erdos952.DiagonalBound.reduce_val
#print axioms Erdos952.DiagonalBound.reduce_add
#print axioms Erdos952.DiagonalBound.residue_add_step
#print axioms Erdos952.DiagonalBound.sieved_of_prime
#print axioms Erdos952.DiagonalBound.potential_difference_of_step
#print axioms Erdos952.DiagonalBound.prime_potential_difference
#print axioms Erdos952.no_bounded_step_sequence_of_bound_le_four
#print axioms Erdos952.five_le_bound_of_witness

example : ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
    ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < 4 :=
  Erdos952.no_bounded_step_sequence_of_bound_le_four (by norm_num)

example (C : ℤ) (hC : C ≤ 4) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hs : ∀ n, (x (n + 1) - x n).norm < C) : False :=
  Erdos952.no_bounded_step_sequence_of_bound_le_four hC
    ⟨x, hx, fun n => ⟨hp n, hs n⟩⟩

example : ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), C ≤ 4 ∧
    Function.Injective x ∧ ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  rintro ⟨x, C, hC, hx, hs⟩
  exact Erdos952.no_bounded_step_sequence_of_bound_le_four hC ⟨x, hx, hs⟩

example {C : ℤ} (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n)) (hs : ∀ n, (x (n + 1) - x n).norm < C) : 5 ≤ C :=
  Erdos952.five_le_bound_of_witness ⟨x, hx, fun n => ⟨hp n, hs n⟩⟩

open Erdos952.DiagonalBound in
example : residue (⟨-1, 0⟩ : GaussianInt) = (64, 0) := by decide +kernel

open Erdos952.DiagonalBound in
example : potential (residue (⟨-1, 0⟩ : GaussianInt)) -
    potential (residue (⟨0, 1⟩ : GaussianInt)) = (⟨-1, -1⟩ : GaussianInt) := by
  decide +kernel
