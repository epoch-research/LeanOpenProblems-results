import Submission.ExplicitPhaseFlattening

/-! A large masked U2 value of a unit local quadratic phase yields an
explicit bounded-rank local linearization. This connects the exact phase
certificate to the new flattening theorem, without assuming derivative data. -/
namespace Erdos3LocalQuadraticU2Linearization
open Finset Erdos3ExplicitPhaseFlattening Erdos3ExactPhaseLinearObstruction
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3LocalQuadraticInverse Erdos3CorrelationSifting Erdos3FiniteBohr
  Erdos3RelativeStableBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma untwist_increment_norm (q : G → ℂ) (ψ : AddChar G ℂ) (b y : G) :
    ‖q (b+y)-q b*ψ y‖ =
      ‖q (b+y)*conj (ψ (b+y))-q b*conj (ψ b)‖ := by
  have hχ : ψ y*conj (ψ (b+y)) = conj (ψ b) := by
    calc
      _ = conj (ψ b)*(ψ y*conj (ψ y)) := by rw [ψ.map_add_eq_mul,map_mul]; ring
      _ = _ := by rw [mul_conj_eq_one (ψ.norm_apply y),mul_one]
  calc
    _ = ‖(q (b+y)-q b*ψ y)*conj (ψ (b+y))‖ := by
      rw [norm_mul,Complex.norm_conj,ψ.norm_apply,mul_one]
    _ = _ := by rw [sub_mul,mul_assoc,hχ]

/-- The input contains only masked U2, local quadraticity, and outer Bohr
stability. The output phase is approximately linear on an explicit refined
window, with one ambient character and <=32/beta^2 new Bohr frequencies. -/
theorem local_quadratic_U2_linearization (D : Finset (AddChar G ℂ))
    {R β σ : ℝ} (hR : 0 < R) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) {o : ℕ} (ho : 0 < o)
    (hst : RelativeStable D o R) (hoB : 1/(o : ℝ) ≤ β/8)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    (hU : β^2*(density (bohr D R))^3 ≤ uniformityPower 1 (mask (bohr D R) q)) :
    ∃ ψ : AddChar G ℂ, ∃ E : Finset (AddChar G ℂ), ∃ s t : ℝ, ∃ b ∈ bohr D R,
      (E.card : ℝ) ≤ 32/β^2 ∧ ((D ∪ E).card : ℝ) ≤ D.card+32/β^2 ∧
      explicitBaseRadius D.card R σ β o ≤ s ∧ explicitStepRadius D.card R σ β o ≤ t ∧
      0 < s ∧ 0 < t ∧
      (∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, (b+x)+y ∈ bohr D R) ∧
      (∀ y ∈ bohr (D ∪ E) t, ‖q (b+y)-q b*ψ y‖ ≤ σ/2) ∧
      ∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, ‖q ((b+x)+y)-q (b+x)*ψ y‖ ≤ σ := by
  have hW : (bohr D R).Nonempty := ⟨0,bohr_zero D hR.le⟩
  have hd := density_pos (bohr D R) hW
  obtain ⟨ψ,hψ⟩ := local_phase_fourier_certificate (bohr D R) hW q hq
  have hh := hU.trans hψ
  have hsq : β^2 ≤ ‖𝔼 x : bohr D R, q x*conj (ψ x)‖^2 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hd 3)).mp
    simpa only [mul_comm (density (bohr D R)^3)] using hh
  have hbias : β ≤ ‖𝔼 x : bohr D R, q x*conj (ψ x)‖ := by
    nlinarith [norm_nonneg (𝔼 x : bohr D R, q x*conj (ψ x))]
  let f : G → ℂ := fun x ↦ q x*conj (ψ x)
  have hf (x : G) : ‖f x‖ = 1 := by simp only [f,norm_mul,Complex.norm_conj,hq,ψ.norm_apply,mul_one]
  have hfquad : IsLocallyQuadratic (bohr D R : Set G) f := by
    simpa only [AddChar.inv_apply,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj] using
      hquad.mul_character ψ⁻¹
  obtain ⟨E,s,t,b,hb,hE,hDE,hsL,htL,hs,ht,hdom,hbase,hall⟩ :=
    explicit_biased_quadratic_flattening D hR hβ hβ1 hσ hσ1 ho hst hoB f hf hfquad hbias
  refine ⟨ψ,E,s,t,b,hb,hE,hDE,hsL,htL,hs,ht,hdom,?_,?_⟩
  · intro y hy
    rw [untwist_increment_norm]
    exact hbase y hy
  · intro x hx y hy
    rw [untwist_increment_norm]
    exact hall x hx y hy

#print axioms local_quadratic_U2_linearization
end Erdos3LocalQuadraticU2Linearization
