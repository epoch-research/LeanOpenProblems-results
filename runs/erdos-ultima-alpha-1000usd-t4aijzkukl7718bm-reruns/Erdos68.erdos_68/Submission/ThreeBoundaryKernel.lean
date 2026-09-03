import Submission.BoundaryPigeonhole

/-! Exact zero-pair kernels for three rational boundary rows. The final
construction supplies a nonzero coefficient pair, not a nonzero real value.
It is auxiliary work and does not settle the conjecture in Spec.lean. -/

namespace ThreeBoundaryKernel

open Finset BoundaryPigeonhole

/-- A cross product of the constant row and the integral boundary row. -/
def kernel (b : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![b 2 - b 1, b 0 - b 2, b 1 - b 0]

/-- When the two boundary differences are coprime, this cross product
parametrizes all integral zero-pair weights, with an integral parameter. -/
theorem zero_pair_iff_multiple (b w : Fin 3 → ℤ)
    (hc : IsCoprime (b 1 - b 0) (b 2 - b 0)) :
    ((∑ i, w i) = 0 ∧ (∑ i, w i * b i) = 0) ↔
      ∃ k : ℤ, ∀ i, w i = k * kernel b i := by
  constructor
  · rintro ⟨hs, hb⟩
    simp only [Fin.sum_univ_three] at hs hb
    obtain ⟨a, c, hac⟩ := hc
    have hr : (b 1 - b 0) * w 1 + (b 2 - b 0) * w 2 = 0 := by
      linear_combination hb - b 0 * hs
    let k := a * w 2 - c * w 1
    have h1 : w 1 = -k * (b 2 - b 0) := by
      dsimp [k]
      linear_combination a * hr - w 1 * hac
    have h2 : w 2 = k * (b 1 - b 0) := by
      dsimp [k]
      linear_combination c * hr - w 2 * hac
    have h0 : w 0 = k * (b 2 - b 1) := by
      linear_combination hs - h1 - h2
    refine ⟨k, ?_⟩
    intro i
    fin_cases i
    · simpa [kernel] using h0
    · change w 1 = k * (b 0 - b 2)
      linear_combination h1
    · simpa [kernel] using h2
  · rintro ⟨k, hk⟩
    constructor <;> simp [Fin.sum_univ_three, hk, kernel] <;> ring

/-- Every nonzero integral zero-pair vector is at least as large, coordinate
by coordinate in absolute value, as the primitive kernel vector. -/
theorem kernel_bound_of_zero_pair (b w : Fin 3 → ℤ) (Q : ℕ)
    (hc : IsCoprime (b 1 - b 0) (b 2 - b 0))
    (hw : w ≠ 0) (hsize : ∀ i, |w i| ≤ Q)
    (hs : (∑ i, w i) = 0) (hb : (∑ i, w i * b i) = 0) :
    ∀ i, |kernel b i| ≤ Q := by
  obtain ⟨k, hk⟩ := (zero_pair_iff_multiple b w hc).mp ⟨hs, hb⟩
  have hk0 : k ≠ 0 := by
    intro h
    apply hw
    funext i
    simpa [h] using hk i
  have hk1 := Int.one_le_abs hk0
  intro i
  have hi := hsize i
  rw [hk i, abs_mul] at hi
  nlinarith [abs_nonneg (kernel b i)]

/-- Pigeonhole clearing cannot produce a zero pair if the primitive kernel
has a coordinate outside the weight box. The value at a real argument is
not asserted to be nonzero. -/
theorem bounded_nonzero_pair (C Q : ℕ) (hC : 0 < C)
    (hcard : C < (Q + 1) ^ 3) (b : Fin 3 → ℤ)
    (hc : IsCoprime (b 1 - b 0) (b 2 - b 0))
    (hlarge : ∃ i, (Q : ℤ) < |kernel b i|) :
    ∃ w : Fin 3 → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ Q) ∧
      ∃ z : ℤ, (∑ i, w i * b i) = C * z ∧
        ((∑ i, w i) ≠ 0 ∨ z ≠ 0) := by
  obtain ⟨w, hw, hsize, z, hz⟩ := bounded_modular_relation 3 C Q hC hcard b
  refine ⟨w, hw, hsize, z, hz, ?_⟩
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := hlarge
  have hb : (∑ i, w i * b i) = 0 := by simpa [h.2] using hz
  exact (not_lt_of_ge (kernel_bound_of_zero_pair b w Q hc hw hsize h.1 hb i)) hi

/-- An analytic specialization with a genuinely nonzero integer coefficient
pair. This does not imply that the displayed error is nonzero. -/
theorem small_nonzero_pair (C Q : ℕ) (hC : 0 < C)
    (hcard : C < (Q + 1) ^ 3) (x η : ℝ)
    (A : ℤ) (hA : A ≠ 0) (B : Fin 3 → ℝ) (b : Fin 3 → ℤ)
    (hclear : ∀ i, (C : ℝ) * B i = b i)
    (hc : IsCoprime (b 1 - b 0) (b 2 - b 0))
    (hlarge : ∃ i, (Q : ℤ) < |kernel b i|)
    (he : ∀ i, |(A : ℝ) * x - B i| ≤ η) :
    ∃ a z : ℤ, (a ≠ 0 ∨ z ≠ 0) ∧ |(a : ℝ) * x - z| ≤ 3 * Q * η := by
  obtain ⟨w, hw, hsize, z, hz, hpair⟩ :=
    bounded_nonzero_pair C Q hC hcard b hc hlarge
  obtain ⟨v, hv⟩ := integral_boundary_of_modular_relation 3 C hC B b w hclear ⟨z, hz⟩
  have hvz : v = z := by
    have hh : (C : ℝ) * (v : ℝ) = C * (z : ℝ) := by
      rw [← hv, Finset.mul_sum]
      calc
        ∑ i, (C : ℝ) * ((w i : ℝ) * B i) =
            ∑ i, (w i : ℝ) * (b i : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hclear i]
          ring
        _ = (C : ℝ) * (z : ℝ) := by exact_mod_cast hz
    have hh' := mul_left_cancel₀ (by positivity : (C : ℝ) ≠ 0) hh
    exact_mod_cast hh'
  subst v
  refine ⟨A * ∑ i, w i, z, ?_, ?_⟩
  · rcases hpair with hs | hz
    · exact Or.inl (mul_ne_zero hA hs)
    · exact Or.inr hz
  · simpa [hv] using weighted_error_bound 3 Q x η A B w hsize he

end ThreeBoundaryKernel

#print axioms ThreeBoundaryKernel.zero_pair_iff_multiple
#print axioms ThreeBoundaryKernel.small_nonzero_pair
