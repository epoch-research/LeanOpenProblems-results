import Submission.LocalQuadraticIntegration

/-! Reindexing the retained twisted energy by opposite-vertex sums exposes
the antisymmetric pairing as the kernel of a quadratic form. -/
namespace Erdos3AntidiagonalTwistedEnergy
open Finset Erdos3FiniteFourier Erdos3SpectralGraphEnergy Erdos3TwistedCorrelationEnergy
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def skewPhase (F : G → AddChar G ℂ) (x y : G) : ℂ := F x y*conj (F y x)
noncomputable def fiberWeight (b : G → ℂ) (F : G → AddChar G ℂ) (s x : G) : ℂ :=
  b x*b (s-x)*F x (x-s)
noncomputable def skewForm (w : G → ℂ) (F : G → AddChar G ℂ) : ℂ :=
  𝔼 x, 𝔼 u, w x*conj (w u)*skewPhase F x u

lemma skewPhase_norm (F : G → AddChar G ℂ) (x y : G) : ‖skewPhase F x y‖ = 1 := by
  simp only [skewPhase,norm_mul,Complex.norm_conj,AddChar.norm_apply,mul_one]

lemma skewPhase_sub_right (T : Finset G) (F : G → AddChar G ℂ)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v)
    (x : G) {u v : G} (hu : u ∈ T) (hv : v ∈ T) :
    skewPhase F x u*conj (skewPhase F x v) = skewPhase F x (u-v) := by
  unfold skewPhase
  rw [hF u hu v hv,char_sub,character_sub_apply]
  simp only [map_mul,starRingEnd_self_apply]
  ring

lemma fiberWeight_support (T : Finset G) (b : G → ℂ) (F : G → AddChar G ℂ)
    (hb : ∀ x, x ∉ T → b x = 0) (s x : G) (hx : x ∉ T) : fiberWeight b F s x = 0 := by
  simp only [fiberWeight,hb x hx,zero_mul]

lemma fiberWeight_norm_le_one (b : G → ℂ) (F : G → AddChar G ℂ)
    (hb : ∀ x, ‖b x‖ ≤ 1) (s x : G) : ‖fiberWeight b F s x‖ ≤ 1 := by
  simp only [fiberWeight,norm_mul,AddChar.norm_apply,mul_one]
  exact (mul_le_mul (hb _) (hb _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

lemma skew_factorization (χ ψ : AddChar G ℂ) (x u s : G) :
    (χ-ψ) (x+u-s) = χ (x-s)*conj (ψ (u-s))*(χ u*conj (ψ x)) := by
  rw [character_sub_apply]
  have hx : χ (x+u-s) = χ (x-s)*χ u := by
    rw [show x+u-s = (x-s)+u by abel,χ.map_add_eq_mul]
  have hu : ψ (x+u-s) = ψ (u-s)*ψ x := by
    rw [show x+u-s = (u-s)+x by abel,ψ.map_add_eq_mul]
  rw [hx,hu,map_mul]
  ring

lemma fiberWeight_factorization (T : Finset G) (b : G → ℂ) (F : G → AddChar G ℂ)
    (hb : ∀ x, x ∉ T → b x = 0)
    (hF : ∀ x ∈ T, ∀ u ∈ T, F (x-u) = F x-F u) (s x u : G) :
    b x*conj (b u)*conj (b (s-u))*b (s-x)*F (x-u) (x+u-s) =
      fiberWeight b F s x*conj (fiberWeight b F s u)*skewPhase F x u := by
  by_cases hx : x ∈ T
  · by_cases hu : u ∈ T
    · rw [hF x hx u hu,skew_factorization]
      simp only [fiberWeight,skewPhase,map_mul]
      ring
    · simp only [hb u hu,fiberWeight,map_mul,map_zero,mul_zero,zero_mul]
  · simp only [hb x hx,fiberWeight,zero_mul]

/-- The antisymmetric kernel is exposed without assuming symmetry or any
additivity away from differences of points in T. -/
theorem twistedEnergy_eq_skew_forms (T : Finset G) (b : G → ℂ) (F : G → AddChar G ℂ)
    (hb : ∀ x, x ∉ T → b x = 0)
    (hF : ∀ x ∈ T, ∀ u ∈ T, F (x-u) = F x-F u) :
    twistedEnergy b F = 𝔼 s, skewForm (fiberWeight b F s) F := by
  unfold twistedEnergy
  calc
    _ = 𝔼 x, 𝔼 u, 𝔼 s,
        b x*conj (b u)*conj (b (s-u))*b (s-x)*F (x-u) (x+u-s) := by
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro u _
      exact (Fintype.expect_equiv (Equiv.subLeft (x+u)) _ _ (fun s ↦ by
        simp only [Equiv.subLeft_apply,show x-(x+u-s) = s-u by abel,
          show u-(x+u-s) = s-x by abel])).symm
    _ = 𝔼 s, 𝔼 x, 𝔼 u,
        b x*conj (b u)*conj (b (s-u))*b (s-x)*F (x-u) (x+u-s) := expect_rotate_three _
    _ = _ := by
      apply expect_congr rfl
      intro s _
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro u _
      exact fiberWeight_factorization T b F hb hF s x u

#print axioms twistedEnergy_eq_skew_forms
end Erdos3AntidiagonalTwistedEnergy
