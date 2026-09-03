import Submission.FixedCenterQuadraticAverage
import Submission.FiniteSampling

/-! A local finite-phase approximation to each stable quadratic average. All
error estimates use normalized window averages, so no inverse window density
enters the sample count. -/
namespace Erdos3SampledQuadraticAverage
open Finset Erdos3FixedCenterQuadraticAverage Erdos3QuadraticAverageDetectors
  Erdos3RelativeStableBohr Erdos3FiniteBohr Erdos3LocalQuadraticInverse
  Erdos3FiniteSampling Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma exists_le_mean {V : Type*} [Fintype V] [Nonempty V] (E : V → ℝ) :
    ∃ v, E v ≤ 𝔼 w, E w := by
  by_contra! h
  have hp := expect_pos (s := (univ : Finset V))
    (f := fun v ↦ E v-(𝔼 w, E w)) (fun v _ ↦ sub_pos.mpr (h v)) univ_nonempty
  rw [expect_sub_distrib,Fintype.expect_const,sub_self] at hp
  exact lt_irrefl 0 hp

/-- Sampling bounded functions on a normalized coordinate space gives the
usual 1/M mean-square error, independent of the number of coordinates. -/
theorem exists_normalized_sample {I A X : Type*}
    [Fintype I] [Nonempty I] [Fintype A] [Nonempty A] [Fintype X] [Nonempty X]
    (f : A → X → ℝ) (hf : ∀ a x, |f a x| ≤ 1) :
    ∃ v : I → A,
      (𝔼 x : X, ((𝔼 i : I, f (v i) x)-(𝔼 a : A, f a x))^2) ≤
        1/(Fintype.card I : ℝ) := by
  classical
  obtain ⟨v,hv⟩ := exists_le_mean
    (fun v : I → A ↦ 𝔼 x : X, ((𝔼 i : I, f (v i) x)-(𝔼 a : A, f a x))^2)
  refine ⟨v,hv.trans ?_⟩
  rw [expect_comm]
  apply expect_le univ_nonempty
  intro x _
  rw [sample_mean_center_sq (I := I) (fun a ↦ f a x)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : (𝔼 a : A, (f a x)^2) ≤ 1 := by
    apply expect_le univ_nonempty
    intro a _
    have hh := abs_le.mp (hf a x)
    nlinarith [hh.1,hh.2]
  nlinarith [sq_nonneg (𝔼 a : A, f a x)]

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def phaseSample {M : ℕ} (v : Fin M → G)
    (q : G → G → ℂ) (b : G → ℂ) (a t : G) : ℝ :=
  𝔼 i : Fin M, (b (a-v i)*conj (q (a-v i) (v i+t))).re

lemma phaseSample_bound {M : ℕ} (hM : 0 < M) (v : Fin M → G)
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a t : G) :
    |phaseSample v q b a t| ≤ 1 := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro i _
  apply (Complex.abs_re_le_norm _).trans
  simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hb (a-v i)

/-- Simultaneously approximates all coordinates in W by one sample of centers. -/
theorem sample_fixed_average (B W : Finset G) (hB : B.Nonempty) (hW : W.Nonempty)
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a : G) {M : ℕ} (hM : 0 < M) :
    ∃ v : Fin M → B,
      (𝔼 t : W, (phaseSample (fun i ↦ (v i : G)) q b a t-
        (fixedAverage B q b a t).re)^2) ≤ 1/(M : ℝ) := by
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty W := hW.to_subtype
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let f : B → W → ℝ := fun y t ↦ (b (a-y)*conj (q (a-y) (y+t))).re
  have hf (y : B) (t : W) : |f y t| ≤ 1 := by
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hb (a-y)
  obtain ⟨v,hv⟩ := exists_normalized_sample (I := Fin M) f hf
  refine ⟨v,?_⟩
  simpa only [phaseSample,fixedAverage,expect_re,Fintype.card_fin,f] using hv

/-- A stable quadratic average admits an M-phase local approximation, with
mean squared error at most 2/z^2+2/M, uniformly in the base point a. -/
theorem sample_stable_average (D : Finset (AddChar G ℂ)) {r : ℝ}
    (hr : 0 < r) {z : ℕ} (hz : 0 < z) (hstable : RelativeStable D z r)
    (W : Finset G) (hW : W.Nonempty) (hsub : W ⊆ bohr D (relativeWidth D z r))
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a : G) {M : ℕ} (hM : 0 < M) :
    ∃ v : Fin M → bohr D r,
      (𝔼 t : W, (realAverage (bohr D r) q b (a+t)-
        phaseSample (fun i ↦ (v i : G)) q b a t)^2) ≤
        2/(z : ℝ)^2+2/(M : ℝ) := by
  letI : Nonempty W := hW.to_subtype
  obtain ⟨v,hv⟩ := sample_fixed_average (bohr D r) W ⟨0,bohr_zero D hr.le⟩ hW q hq b hb a hM
  refine ⟨v,?_⟩
  have he (t : W) :
      (realAverage (bohr D r) q b (a+t)-phaseSample (fun i ↦ (v i : G)) q b a t)^2 ≤
      2/(z : ℝ)^2+2*(phaseSample (fun i ↦ (v i : G)) q b a t-
        (fixedAverage (bohr D r) q b a t).re)^2 := by
    have ht := stable_fixed_real_approximation D hr hz hstable q hq b hb a (hsub t.property)
    have hs : (realAverage (bohr D r) q b (a+t)-(fixedAverage (bohr D r) q b a t).re)^2 ≤
        (1/(z : ℝ))^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
    have hsplit := sq_nonneg
      (realAverage (bohr D r) q b (a+t)-(fixedAverage (bohr D r) q b a t).re+
        (phaseSample (fun i ↦ (v i : G)) q b a t-(fixedAverage (bohr D r) q b a t).re))
    rw [div_pow,one_pow] at hs
    simp only [div_eq_mul_inv,one_mul] at hs ⊢
    nlinarith only [hs,hsplit]
  calc
    _ ≤ 𝔼 t : W, (2/(z : ℝ)^2+2*(phaseSample (fun i ↦ (v i : G)) q b a t-
        (fixedAverage (bohr D r) q b a t).re)^2) := expect_le_expect (fun t _ ↦ he t)
    _ = 2/(z : ℝ)^2+2*(𝔼 t : W, (phaseSample (fun i ↦ (v i : G)) q b a t-
        (fixedAverage (bohr D r) q b a t).re)^2) := by
      rw [expect_add_distrib,Fintype.expect_const,← mul_expect]
    _ ≤ _ := by
      simp only [div_eq_mul_inv,one_mul] at hv ⊢
      linarith

/-- A finite local factor representation, with M unit quadratic coordinates and
bounded coefficients. The mean-square error is independent of |G| and |W|. -/
theorem stable_average_local_factor (D : Finset (AddChar G ℂ)) {r : ℝ}
    (hr : 0 < r) (hrmax : r ≤ 1/32) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable D z r)
    (W : Finset G) (hW : W.Nonempty) (hsub : W ⊆ bohr D (relativeWidth D z r))
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (hquad : ∀ a, IsLocallyQuadratic (bohr D (1/16) : Set G) (q a))
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a : G) {M : ℕ} (hM : 0 < M) :
    ∃ c : Fin M → ℂ, ∃ Q : Fin M → G → ℂ,
      (∀ i, ‖c i‖ ≤ 1) ∧ (∀ i t, ‖Q i t‖ = 1) ∧
      (∀ i, IsLocallyQuadratic (W : Set G) (Q i)) ∧
      (𝔼 t : W, (realAverage (bohr D r) q b (a+t)-
        (𝔼 i : Fin M, (c i*conj (Q i t)).re))^2) ≤
        2/(z : ℝ)^2+2/(M : ℝ) := by
  obtain ⟨v,hv⟩ := sample_stable_average D hr hz hstable W hW hsub q hq b hb a hM
  refine ⟨fun i ↦ b (a-v i),fun i t ↦ q (a-v i) ((v i : G)+t),
    fun i ↦ hb _,fun i t ↦ hq _ _,?_,hv⟩
  intro i
  have hQi := shifted_phase_quadratic D hr.le hrmax hz q hquad a (v i).property
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  exact hQi x h k l (hsub hx) (hsub hxh) (hsub hxk) (hsub hxkh)
    (hsub hxl) (hsub hxlh) (hsub hxlk) (hsub hxlkh)

#print axioms exists_normalized_sample
#print axioms sample_stable_average
#print axioms stable_average_local_factor
end Erdos3SampledQuadraticAverage
