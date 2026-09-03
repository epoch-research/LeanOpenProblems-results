import Submission.PolynomialSquareValues

/-! Positive and negative controls for the scope of the square-value theorem. -/
namespace Erdos213.PolynomialSquareValuesTests
open Polynomial PolynomialSquareValues

private def pell : ℕ → ℕ × ℕ
  | 0 => (0,1)
  | n+1 => (3*(pell n).1+2*(pell n).2,4*(pell n).1+3*(pell n).2)

private lemma pell_eq (n : ℕ) : (pell n).2^2=2*(pell n).1^2+1 := by
  induction n with
  | zero => norm_num [pell]
  | succ n ih =>
    simp only [pell]
    nlinarith only [ih]

private lemma pell_pos (n : ℕ) : 0 < (pell n).2 := by
  have h := pell_eq n
  nlinarith only [h]

private lemma pell_strict : StrictMono (fun n => (pell n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [pell]
  have h := pell_pos n
  omega

/-- Infinitely many square values do not imply a square polynomial. This
control explains why the eventual-universal hypothesis cannot be weakened. -/
theorem infinite_square_values_not_square :
    ¬ IsSquare (2*X^2+1 : ℚ[X]) ∧
      Set.Infinite {n : ℤ | IsSquare ((2*X^2+1 : ℚ[X]).eval (n : ℚ))} := by
  constructor
  · intro h
    have hh := h.map (evalRingHom (1 : ℚ))
    norm_num at hh
  · have hinj : Function.Injective (fun n : ℕ => ((pell n).1 : ℤ)) :=
      Int.ofNat_injective.comp pell_strict.injective
    apply (Set.infinite_range_of_injective hinj).mono
    rintro n ⟨k,rfl⟩
    refine ⟨((pell k).2 : ℚ),?_⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
    have hh : ((pell k).2 : ℚ)^2=2*((pell k).1 : ℚ)^2+1 := by
      exact_mod_cast pell_eq k
    push_cast
    nlinarith only [hh]

/-- Exercise the rational-denominator branch of the general theorem. -/
theorem rational_denominator_control : IsSquare (C (1/9 : ℚ)*(X^2+1)^2) := by
  apply isSquare_of_eventually_int_eval
  refine ⟨4,?_⟩
  intro n _
  refine ⟨((n : ℚ)^2+1)/3,?_⟩
  simp only [eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_C]
  norm_num
  ring

#print axioms infinite_square_values_not_square
#print axioms rational_denominator_control
end Erdos213.PolynomialSquareValuesTests
