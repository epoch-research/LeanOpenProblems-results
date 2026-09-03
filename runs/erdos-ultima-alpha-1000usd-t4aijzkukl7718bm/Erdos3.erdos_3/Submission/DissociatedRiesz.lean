import FormalConjecturesUtil

/-! Exact L² identity for a product over dissociated characters.
This is auxiliary harmonic analysis, not the original conjecture. -/
namespace Erdos3DissociatedRiesz
open Finset
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 1500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma expect_char_mul_conj (χ ψ : AddChar G ℂ) :
    (𝔼 x : G, χ x * conj (ψ x)) = if χ = ψ then 1 else 0 := by
  simpa only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply, eq_comm] using
    AddChar.wInner_cWeight_eq_boole ψ χ

lemma expect_energy_sum_chars {I : Type*} (u : Finset I)
    (χ : I → AddChar G ℂ) (c : I → ℂ) (hχ : (u : Set I).InjOn χ) :
    (𝔼 x : G, (∑ i ∈ u, c i*χ i x)*conj (∑ i ∈ u, c i*χ i x)) =
      ∑ i ∈ u, c i*conj (c i) := by
  simp_rw [map_sum, sum_mul, mul_sum, expect_sum_comm, map_mul]
  have hterm (i j : I) :
      (𝔼 x : G, c i*χ i x*(conj (c j)*conj (χ j x))) =
        (c i*conj (c j))*(if χ i = χ j then 1 else 0) := by
    have hr (x : G) : c i*χ i x*(conj (c j)*conj (χ j x)) =
        (c i*conj (c j))*(χ i x*conj (χ j x)) := by ring
    simp_rw [hr]
    rw [← mul_expect, expect_char_mul_conj]
  simp_rw [hterm]
  apply sum_congr rfl
  intro i hi
  calc
    _ = ∑ j ∈ u, (c i*conj (c j))*(if i = j then 1 else 0) := by
      apply sum_congr rfl
      intro j hj
      have hh : χ i = χ j ↔ i = j := ⟨hχ hi hj, fun h ↦ congrArg χ h⟩
      simp only [hh]
    _ = c i*conj (c i) := by simp [hi]

lemma expect_norm_sq_sum_chars {I : Type*} (u : Finset I)
    (χ : I → AddChar G ℂ) (c : I → ℂ) (hχ : (u : Set I).InjOn χ) :
    (𝔼 x : G, ‖∑ i ∈ u, c i*χ i x‖^2) = ∑ i ∈ u, ‖c i‖^2 := by
  have he := congrArg Complex.re (expect_energy_sum_chars u χ c hχ)
  have hreal (z : ℂ) : (z*conj z).re = ‖z‖^2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hre (f : G → ℂ) : (𝔼 x, f x).re = 𝔼 x, (f x).re :=
    map_expect (Complex.reCLM.toLinearMap.restrictScalars ℚ≥0) f univ
  rw [hre, Complex.re_sum] at he
  simpa only [Complex.reCLM_apply, hreal] using he

/-- Dissociation of the character set makes all distinct subset-products orthogonal. -/
theorem riesz_l2 (D : Finset (AddChar G ℂ)) (hD : MulDissociated (D : Set (AddChar G ℂ)))
    (a : AddChar G ℂ → ℂ) :
    (𝔼 x : G, ‖∏ χ ∈ D, (1+a χ*χ x)‖^2) = ∏ χ ∈ D, (1+‖a χ‖^2) := by
  have hinj : (D.powerset : Set (Finset (AddChar G ℂ))).InjOn
      (fun t ↦ ∏ χ ∈ t, χ) := by
    intro t ht u hu htu
    exact hD (by simpa using ht) (by simpa using hu) htu
  have hprod (x : G) : (∏ χ ∈ D, (1+a χ*χ x)) =
      ∑ t ∈ D.powerset, (∏ χ ∈ t, a χ)*(∏ χ ∈ t, χ) x := by
    rw [prod_one_add]
    simp only [prod_mul_distrib, AddChar.prod_apply]
  simp_rw [hprod]
  rw [expect_norm_sq_sum_chars D.powerset _ _ hinj, prod_one_add]
  apply sum_congr rfl
  intro t _
  rw [norm_prod, prod_pow]

#print axioms riesz_l2
end Erdos3DissociatedRiesz
