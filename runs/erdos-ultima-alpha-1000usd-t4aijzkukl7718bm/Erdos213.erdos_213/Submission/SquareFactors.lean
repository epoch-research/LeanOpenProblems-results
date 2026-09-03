import FormalConjecturesUtil

/-! Exact rational-distance candidates obtained by allowing square factors.
These lemmas do not assert the existence of large general-position sets. -/

namespace Erdos213.SquareFactors

def RationalNorm (z : ℂ) : Prop := ∃ q : ℚ, (q : ℝ) = ‖z‖

/-- The norm of a square is rational whenever its squared norm is rational.
The norm of the unsquared number itself need not be rational. -/
lemma rationalNorm_sq (z : ℂ) (q : ℚ) (hq : Complex.normSq z = (q : ℝ)) :
    RationalNorm (z ^ 2) := by
  refine ⟨q, ?_⟩
  rw [norm_pow, Complex.sq_norm, hq]

noncomputable def candidate (u : ℂ) : ℂ := (2*u/(1+u^2))^2

lemma normSq_one_add_sq (u : ℂ) (r s : ℚ)
    (hr : u.re = (r : ℝ)) (hs : Complex.normSq u = (s : ℝ)) :
    Complex.normSq (1+u^2) = (((s-1)^2+4*r^2 : ℚ) : ℝ) := by
  have hu2 : (u^2).re = 2*(r : ℝ)^2-s := by
    have h := hs
    simp only [Complex.normSq_apply, hr] at h
    simp only [pow_two, Complex.mul_re, hr]
    nlinarith
  rw [Complex.normSq_add, map_one, map_pow, hs]
  simp only [one_mul, Complex.conj_re, hu2]
  push_cast
  ring

lemma normSq_one_sub_sq (u : ℂ) (r s : ℚ)
    (hr : u.re = (r : ℝ)) (hs : Complex.normSq u = (s : ℝ)) :
    Complex.normSq (1-u^2) = (((s+1)^2-4*r^2 : ℚ) : ℝ) := by
  have hu2 : (u^2).re = 2*(r : ℝ)^2-s := by
    have h := hs
    simp only [Complex.normSq_apply, hr] at h
    simp only [pow_two, Complex.mul_re, hr]
    nlinarith
  rw [Complex.normSq_sub, map_one, map_pow, hs]
  simp only [one_mul, Complex.conj_re, hu2]
  push_cast
  ring

/-- Explicit rational values for the distances from the candidate to 0 and 1.
No rationality assumption on `‖u‖` is needed. -/
lemma candidate_distances (u : ℂ) (r s : ℚ)
    (hr : u.re = (r : ℝ)) (hs : Complex.normSq u = (s : ℝ))
    (hd : 1+u^2 ≠ 0) :
    dist (candidate u) 0 = (((4*s)/((s-1)^2+4*r^2) : ℚ) : ℝ) ∧
    dist (candidate u) 1 = ((((s+1)^2-4*r^2)/((s-1)^2+4*r^2) : ℚ) : ℝ) := by
  have hn : Complex.normSq (2*u) = ((4*s : ℚ) : ℝ) := by
    rw [map_mul, hs]
    norm_num [Complex.normSq_apply]
  have hf : 1-candidate u = ((1-u^2)/(1+u^2))^2 := by
    dsimp [candidate]
    field_simp [hd]
    ring
  constructor
  · rw [dist_zero_right]
    dsimp [candidate]
    rw [norm_pow, Complex.sq_norm, Complex.normSq_div, hn, normSq_one_add_sq u r s hr hs]
    push_cast
    rfl
  · rw [dist_comm, dist_eq_norm, hf, norm_pow, Complex.sq_norm, Complex.normSq_div,
      normSq_one_sub_sq u r s hr hs, normSq_one_add_sq u r s hr hs]
    push_cast
    rfl

lemma candidate_rational_distances (u : ℂ) (r s : ℚ)
    (hr : u.re = (r : ℝ)) (hs : Complex.normSq u = (s : ℝ)) :
    RationalNorm (candidate u) ∧ RationalNorm (1-candidate u) := by
  by_cases hd : 1+u^2 = 0
  · simp [candidate, hd, RationalNorm]
    exact ⟨1, by norm_num⟩
  · obtain ⟨h₀,h₁⟩ := candidate_distances u r s hr hs hd
    constructor
    · exact ⟨4*s/((s-1)^2+4*r^2), by simpa using h₀.symm⟩
    · exact ⟨((s+1)^2-4*r^2)/((s-1)^2+4*r^2), by
        simpa only [dist_eq_norm, norm_sub_rev] using h₁.symm⟩

#print axioms candidate_distances
#print axioms candidate_rational_distances

end Erdos213.SquareFactors
