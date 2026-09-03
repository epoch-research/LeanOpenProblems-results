import FormalConjecturesUtil

/-! Square classes in the proposed rational-median fibration.
These are algebraic tools, not an existence or nonexistence theorem for
arbitrary rational-distance configurations. -/

namespace Erdos213.BiquadraticSquares

open QuadraticAlgebra Polynomial

lemma quadratic_square_iff {K : Type*} [Field K] [CharZero K]
    (a d : K) (ha : a ≠ 0) :
    IsSquare (algebraMap K (QuadraticAlgebra K a 0) d) ↔
      IsSquare d ∨ IsSquare (a*d) := by
  constructor
  · rintro ⟨z,hz⟩
    have hr := congrArg QuadraticAlgebra.re hz
    have hi := congrArg QuadraticAlgebra.im hz
    simp only [algebraMap_re, re_mul] at hr
    simp only [algebraMap_im, im_mul, zero_mul, add_zero] at hi
    have hprod : z.re*z.im = 0 := by
      have he : (2 : K)*(z.re*z.im) = 0 := by linear_combination -hi
      exact (mul_eq_zero.mp he).resolve_left (by norm_num)
    rcases mul_eq_zero.mp hprod with hre | him
    · right
      refine ⟨a*z.im, ?_⟩
      rw [hre] at hr
      linear_combination a*hr
    · left
      exact ⟨z.re, by simpa [him] using hr⟩
  · rintro (⟨z,hz⟩ | ⟨z,hz⟩)
    · exact ⟨algebraMap K (QuadraticAlgebra K a 0) z, by simp [hz]⟩
    · refine ⟨⟨0,z/a⟩, ?_⟩
      ext
      · simp
        field_simp
        linear_combination hz
      · simp

lemma biquadratic_square_iff {K : Type*} [Field K] [CharZero K]
    (a b d : K) (ha : ¬ IsSquare a) (hb : b ≠ 0) :
    IsSquare
      (algebraMap (QuadraticAlgebra K a 0)
        (QuadraticAlgebra (QuadraticAlgebra K a 0)
          (algebraMap K (QuadraticAlgebra K a 0) b) 0)
        (algebraMap K (QuadraticAlgebra K a 0) d)) ↔
      IsSquare d ∨ IsSquare (a*d) ∨ IsSquare (b*d) ∨ IsSquare (a*(b*d)) := by
  letI : Fact (∀ r : K, r^2 ≠ a+0*r) := ⟨by
    intro r hr
    apply ha
    exact ⟨r, by simpa [pow_two] using hr.symm⟩⟩
  have ha0 : a ≠ 0 := by
    intro h
    exact ha ⟨0, by simp [h]⟩
  have hb0 : algebraMap K (QuadraticAlgebra K a 0) b ≠ 0 := by
    intro h
    have hh := congrArg QuadraticAlgebra.re h
    exact hb (by simpa using hh)
  rw [quadratic_square_iff _ _ hb0, ← map_mul,
    quadratic_square_iff a d ha0, quadratic_square_iff a (b*d) ha0]
  tauto

lemma squarefree_dvd_of_square_mul {K : Type*} [Field K]
    {D Q : K[X]} (hD : Squarefree D) (h : IsSquare (D*Q)) : D ∣ Q := by
  obtain ⟨p,hp⟩ := h
  have hd : D ∣ p^2 := by
    rw [pow_two, ← hp]
    exact dvd_mul_right D Q
  obtain ⟨r,hr⟩ := (hD.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hd
  refine ⟨r*r, ?_⟩
  apply mul_left_cancel₀ hD.ne_zero
  rw [hp, hr]
  ring

#print axioms quadratic_square_iff
#print axioms biquadratic_square_iff
#print axioms squarefree_dvd_of_square_mul

end Erdos213.BiquadraticSquares
