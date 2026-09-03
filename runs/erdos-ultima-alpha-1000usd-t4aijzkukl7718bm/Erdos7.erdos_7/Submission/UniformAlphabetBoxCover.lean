import Submission.GenericBoxRandomCover

/-! A counterexample to an arithmetic-free version of the proposed weighted
core bound. There is an atomic box cover with distinct supports on 160 equal
alphabets of size18, although the product budget with weights2/17^2 is below1.
Equal alphabets here correspond to REPEATING the prime19. Thus this does not
satisfy the distinct-prime hypothesis and does not settle Erdős7. -/
namespace Erdos7UniformAlphabetBoxCover
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Support := {s : Finset (Fin 160) // s.card = 8}

lemma alphabet_exp_bound : (18 : ℝ) ≤ Real.exp 4 := by
  have h : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    convert Real.add_one_le_exp (1 / 2 : ℝ) using 1 <;> norm_num
  calc
    (18 : ℝ) ≤ (3 / 2 : ℝ)^8 := by norm_num
    _ ≤ (Real.exp (1 / 2))^8 := pow_le_pow_left₀ (by norm_num) h 8
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num

lemma grid_exp_bound : (18 : ℝ)^160 ≤ Real.exp 640 := by
  calc
    (18 : ℝ)^160 ≤ (Real.exp 4)^160 := pow_le_pow_left₀ (by norm_num) alphabet_exp_bound _
    _ = Real.exp 640 := by rw [← Real.exp_nat_mul]; norm_num

lemma volume_bound : (640 : ℝ) < (Nat.choose 160 8 : ℝ) / (18 : ℝ)^8 := by
  rw [Nat.choose_eq_factorial_div_factorial (by decide : 8 ≤ 160)]
  norm_num [Nat.factorial]

/-- This existential is obtained by a finite counting argument, not a trusted
external randomized or SAT computation. -/
theorem exists_cover :
    ∃ a : Support → Fin 160 → Fin 18,
      ∀ x : Fin 160 → Fin 18, ∃ s, ∀ i ∈ s.val, x i = a s i :=
  Erdos7GenericBoxRandomCover.exists_fixed_size_box_cover
    160 18 8 (by decide) 640 grid_exp_bound volume_bound

lemma support_injective : Function.Injective (Subtype.val : Support → Finset (Fin 160)) :=
  Subtype.val_injective

lemma support_nonunary (s : Support) : 2 ≤ s.val.card := by rw [s.property]; decide

/-- The same budget expression as in the candidate signature method, with
p=19 at every coordinate. Primality alone does not suffice; distinctness matters. -/
lemma repeated_prime_budget_lt_one :
    (∏ _ : Fin 160, (1 + 2 / ((19 : ℝ) - 2)^2)) - 1 -
      (∑ _ : Fin 160, 2 / ((19 : ℝ) - 2)^2) < 1 := by
  norm_num [prod_const, sum_const]

/-- A box cover and a strictly subunit numerical budget coexist when the
coordinate prime may repeat. This is not a StrictCoveringSystem of integers. -/
theorem cover_with_subunit_budget :
    (∃ a : Support → Fin 160 → Fin 18,
      ∀ x : Fin 160 → Fin 18, ∃ s, ∀ i ∈ s.val, x i = a s i) ∧
    (∏ _ : Fin 160, (1 + 2 / ((19 : ℝ) - 2)^2)) - 1 -
      (∑ _ : Fin 160, 2 / ((19 : ℝ) - 2)^2) < 1 :=
  ⟨exists_cover, repeated_prime_budget_lt_one⟩

#print axioms exists_cover
#print axioms repeated_prime_budget_lt_one
#print axioms cover_with_subunit_budget
end Erdos7UniformAlphabetBoxCover
