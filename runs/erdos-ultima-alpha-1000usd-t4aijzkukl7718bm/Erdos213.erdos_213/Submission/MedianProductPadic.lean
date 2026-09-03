import Submission.MedianProductInverse
import Submission.MedianLocalControl
import Mathlib.NumberTheory.Padics.RingHoms

/-! A genuine local counterexample to an automatic median-product inverse.
The positive-area rational-side triangle (14,12,15) satisfies all median
and discriminant square conditions over Q_23, but has no product preimage
over Q_23. It is NOT a rational solution of the median arithmetic problem. -/
namespace Erdos213.MedianProduct
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000

lemma hensel_square_unit {p : ℕ} [Fact p.Prime] (N r : ℤ)
    (hdiv : (p : ℤ) ∣ N-r^2) (hc : IsCoprime (2*r) (p : ℤ)) :
    IsSquare (N : ℤ_[p]) := by
  let F : Polynomial ℤ_[p] := X^2-C (N : ℤ_[p])
  have hF (z : ℤ_[p]) : F.aeval z=z^2-(N : ℤ_[p]) := by simp [F]
  have hder : F.derivative.aeval (r : ℤ_[p])=2*(r : ℤ_[p]) := by
    dsimp [F]
    rw [derivative_sub,derivative_C,derivative_X_pow]
    simp
  have hval : F.aeval (r : ℤ_[p])= -((N-r^2 : ℤ) : ℤ_[p]) := by
    rw [hF]
    push_cast
    ring
  have hu : ‖2*(r : ℤ_[p])‖=1 := by
    simpa only [Int.cast_mul,Int.cast_ofNat] using
      (PadicInt.norm_intCast_eq_one_iff (p := p)).mpr hc
  have hclose : ‖F.aeval (r : ℤ_[p])‖ < ‖F.derivative.aeval (r : ℤ_[p])‖^2 := by
    rw [hval,norm_neg,hder,hu,one_pow]
    exact PadicInt.norm_intCast_lt_one_iff.mpr hdiv
  obtain ⟨z,hz,-⟩ := hensels_lemma hclose
  refine ⟨z,?_⟩
  rw [hF] at hz
  simpa only [pow_two] using (sub_eq_zero.mp hz).symm

local instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

lemma control_local_squares_int :
    IsSquare (542 : ℤ_[23]) ∧ IsSquare (698 : ℤ_[23]) ∧
    IsSquare (455 : ℤ_[23]) ∧ IsSquare (5053 : ℤ_[23]) := by
  refine ⟨hensel_square_unit 542 6 (by norm_num) ?_,
    hensel_square_unit 698 10 (by norm_num) ?_,
    hensel_square_unit 455 8 (by norm_num) ?_,
    hensel_square_unit 5053 4 (by norm_num) ?_⟩
  all_goals norm_num [Int.isCoprime_iff_gcd_eq_one]

lemma control_local_squares :
    IsSquare (542 : ℚ_[23]) ∧ IsSquare (698 : ℚ_[23]) ∧
    IsSquare (455 : ℚ_[23]) ∧ IsSquare (5053 : ℚ_[23]) := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := control_local_squares_int
  refine ⟨?_,?_,?_,?_⟩
  · simpa using h₀.map PadicInt.Coe.ringHom
  · simpa using h₁.map PadicInt.Coe.ringHom
  · simpa using h₂.map PadicInt.Coe.ringHom
  · simpa using h₃.map PadicInt.Coe.ringHom

/-- Integrality is proved before reducing modulo 23. In particular the
argument does not assume that a putative Q_23 preimage is already integral. -/
lemma no_inverse_invariants_padic :
    ¬ ∃ d S : ℚ_[23], d^2=5053 ∧ S^2=565+2*d := by
  rintro ⟨d,S,hd,hs⟩
  have hdn2 : ‖d‖^2 ≤ 1 := by
    rw [← norm_pow,hd]
    simpa using Padic.norm_int_le_one (p := 23) (5053 : ℤ)
  have hdn : ‖d‖ ≤ 1 := by nlinarith [norm_nonneg d]
  let D : ℤ_[23] := ⟨d,hdn⟩
  have hsn2 : ‖S^2‖ ≤ 1 := by
    rw [hs]
    exact (565+2*D : ℤ_[23]).property
  have hsn : ‖S‖ ≤ 1 := by
    rw [norm_pow] at hsn2
    nlinarith [norm_nonneg S]
  let T : ℤ_[23] := ⟨S,hsn⟩
  have hdI : D^2=5053 := by
    apply PadicInt.ext
    exact hd
  have hsI : T^2=565+2*D := by
    apply PadicInt.ext
    exact hs
  apply no_inverse_invariants_mod23
  refine ⟨PadicInt.toZMod D,PadicInt.toZMod T,?_,?_⟩
  · simpa only [map_pow,map_ofNat] using congrArg PadicInt.toZMod hdI
  · simpa only [map_pow,map_add,map_mul,map_ofNat] using congrArg PadicInt.toZMod hsI

lemma no_product_preimage_padic :
    ¬ ∃ A B C : ℚ_[23], productSq A B C=14^2 ∧
      productSq B A C=12^2 ∧ productSq C A B=15^2 := by
  rintro ⟨A,B,C,hP,hQ,hR⟩
  obtain ⟨hd,hs⟩ := necessary_invariants (14^2) (12^2) (15^2) A B C hP hQ hR
  apply no_inverse_invariants_padic
  refine ⟨deltaSq A B C,A+B+C,?_,?_⟩
  · norm_num [deltaSq] at hd ⊢
    exact hd
  · norm_num at hs ⊢
    exact hs

lemma normalized_local_squares :
    MedianLocalControl.SixSquares ((14/12 : ℚ_[23])^2) ((15/12 : ℚ_[23])^2) := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := control_local_squares
  apply MedianLocalControl.normalized_squares (by norm_num : (12 : ℚ_[23]) ≠ 0)
  · norm_num [MedianLocalControl.med₀]
    exact h₂
  · norm_num [MedianLocalControl.med₁]
    exact h₁
  · norm_num [MedianLocalControl.med₂]
    exact h₀
  · norm_num [MedianLocalControl.delta]
    exact h₃

lemma control_positive_area :
    0 < MedianDiscriminant.heron ((14/12 : ℚ)^2) ((15/12 : ℚ)^2) := by
  norm_num [MedianDiscriminant.heron]

lemma control_not_rational :
    ¬ MedianDiscriminant.Admissible ((14/12 : ℚ)^2) ((15/12 : ℚ)^2) := by
  intro h
  have hh := h.2.2.1
  norm_num at hh

/-- All local square conditions and positive real area hold, but the
quadratic product map still has no inverse over this local field. -/
theorem local_inverse_counterexample :
    MedianLocalControl.SixSquares ((14/12 : ℚ_[23])^2) ((15/12 : ℚ_[23])^2) ∧
    0 < MedianDiscriminant.heron ((14/12 : ℚ)^2) ((15/12 : ℚ)^2) ∧
    ¬ (∃ A B C : ℚ_[23], productSq A B C=14^2 ∧
      productSq B A C=12^2 ∧ productSq C A B=15^2) := by
  exact ⟨normalized_local_squares,control_positive_area,no_product_preimage_padic⟩

#print axioms hensel_square_unit
#print axioms control_local_squares
#print axioms no_product_preimage_padic
#print axioms control_not_rational
#print axioms local_inverse_counterexample
end
end Erdos213.MedianProduct
