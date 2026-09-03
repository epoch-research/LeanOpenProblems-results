import Submission.ChangSpectrum

/-! Approximate orthogonality and relative Riesz-product estimates.
These are auxiliary results, not a proof of the Erdős conjecture. -/
namespace Erdos3RelativeRiesz
open Finset Erdos3DissociatedRiesz Erdos3ChangAnalytic Erdos3ChangSpectrum
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Approximate orthogonality of distinct subset products on a reference set. -/
def ApproxDissociated (C : Finset G) (ε : ℝ) (D : Finset (AddChar G ℂ)) : Prop :=
  ∀ s ⊆ D, ∀ t ⊆ D, s ≠ t →
    ‖𝔼 x : C, (∏ χ ∈ s, χ) x * conj ((∏ χ ∈ t, χ) x)‖ ≤ ε

lemma ApproxDissociated.mono {C : Finset G} {ε : ℝ}
    {D E : Finset (AddChar G ℂ)} (hD : ApproxDissociated C ε D) (hED : E ⊆ D) :
    ApproxDissociated C ε E := by
  intro s hs t ht hst
  exact hD s (hs.trans hED) t (ht.trans hED) hst

lemma expect_norm_sq_sum_chars_le (C : Finset G) (hC : C.Nonempty)
    {I : Type*} (u : Finset I) (χ : I → AddChar G ℂ) (a : I → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (horth : ∀ i ∈ u, ∀ j ∈ u, i ≠ j →
      ‖𝔼 x : C, χ i x * conj (χ j x)‖ ≤ ε) :
    (𝔼 x : C, ‖∑ i ∈ u, a i * χ i x‖^2) ≤
      (∑ i ∈ u, ‖a i‖^2) + ε*(∑ i ∈ u, ‖a i‖)^2 := by
  letI : Nonempty C := hC.to_subtype
  have hr (z : ℂ) : ‖z‖^2 = (z*conj z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have he : (𝔼 x : C, ‖∑ i ∈ u, a i*χ i x‖^2) =
      ∑ i ∈ u, ∑ j ∈ u,
        ((a i*conj (a j))*(𝔼 x : C, χ i x*conj (χ j x))).re := by
    simp_rw [hr, map_sum, sum_mul, mul_sum, map_mul, Complex.re_sum,
      expect_sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [← expect_re, mul_expect]
    congr 2
    funext x
    ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ u, ∑ j ∈ u,
        ((if i = j then ‖a i‖^2 else 0) + ε*‖a i‖*‖a j‖) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        simp only [↓reduceIte]
        have hc : (𝔼 x : C, χ i x * conj (χ i x)) = 1 := by
          have hh (x : C) : χ i x * conj (χ i x) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, (χ i).norm_apply]
            norm_num
          simp_rw [hh]
          exact Fintype.expect_const _
        rw [hc, mul_one, ← hr]
        exact le_add_of_nonneg_right (by positivity)
      · simp only [hij, ↓reduceIte, zero_add]
        calc
          _ ≤ ‖(a i*conj (a j))*(𝔼 x : C, χ i x*conj (χ j x))‖ :=
            Complex.re_le_norm _
          _ ≤ (‖a i‖*‖a j‖)*ε := by
            rw [norm_mul, norm_mul, Complex.norm_conj]
            exact mul_le_mul_of_nonneg_left (horth i hi j hj hij) (by positivity)
          _ = _ := by ring
    _ = _ := by
      simp_rw [sum_add_distrib]
      simp only [sum_ite_eq]
      have hsum : (∑ i ∈ u, if i ∈ u then ‖a i‖^2 else 0) = ∑ i ∈ u, ‖a i‖^2 := by
        apply sum_congr rfl
        intro i hi
        simp only [if_pos hi]
      rw [hsum]
      simp_rw [← mul_sum]
      rw [← sum_mul, ← mul_sum]
      ring

/-- The global exact Riesz identity persists up to an explicit local error. -/
theorem relative_riesz_l2 (C : Finset G) (hC : C.Nonempty)
    (D : Finset (AddChar G ℂ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hD : ApproxDissociated C ε D) (a : AddChar G ℂ → ℂ) :
    (𝔼 x : C, ‖∏ χ ∈ D, (1+a χ*χ x)‖^2) ≤
      (∏ χ ∈ D, (1+‖a χ‖^2)) + ε*(∏ χ ∈ D, (1+‖a χ‖))^2 := by
  have hprod (x : G) : (∏ χ ∈ D, (1+a χ*χ x)) =
      ∑ t ∈ D.powerset, (∏ χ ∈ t, a χ)*(∏ χ ∈ t, χ) x := by
    rw [prod_one_add]
    simp only [prod_mul_distrib, AddChar.prod_apply]
  simp_rw [hprod]
  have hh := expect_norm_sq_sum_chars_le C hC D.powerset
    (fun t ↦ ∏ χ ∈ t, χ) (fun t ↦ ∏ χ ∈ t, a χ) hε
    (fun s hs t ht hst ↦ hD s (mem_powerset.mp hs) t (mem_powerset.mp ht) hst)
  simpa only [norm_prod, prod_pow, prod_one_add] using hh

#print axioms relative_riesz_l2
end Erdos3RelativeRiesz
