import Submission.NormalizedQuadraticPowerBounds
import Submission.NormalizedPhaseIncrement
import Submission.InteriorQuadraticDensityIncrement

/-! Polynomial RELATIVE density increments on local quadratic phase cells.
This is a global-to-local step, not an iteration theorem within existing cells. -/
namespace Erdos3NormalizedQuadraticDensityIncrement
open Finset Erdos3NormalizedPhaseIncrement Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
  Erdos3InteriorQuadraticDensityIncrement Erdos3NormalizedQuadraticInverse
  Erdos3NormalizedQuadraticPowerBounds Erdos3FiniteBohr Erdos3FiniteUniformity
  Erdos3CorrelationSifting Erdos3LocalQuadraticInverse Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def liftedPhaseCell (Q : Finset G) (n : ℕ) (q : G → ℂ) (i : PhaseGrid n) : Finset G :=
  (phaseCell n (fun x : Q ↦ q x) i).image Subtype.val

lemma liftedPhaseCell_shape (Q : Finset G) (n : ℕ) (q : G → ℂ) (i : PhaseGrid n) :
    IsInteriorPhaseCell n Q q (liftedPhaseCell Q n q i) := by
  refine ⟨i,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨y.property,(mem_filter.mp hy).2⟩
  · intro hx
    obtain ⟨hx,hcond⟩ := mem_filter.mp hx
    exact mem_image.mpr ⟨⟨x,hx⟩,mem_filter.mpr ⟨mem_univ _,hcond⟩,rfl⟩

lemma liftedPhaseCell_card (Q : Finset G) (n : ℕ) (q : G → ℂ) (i : PhaseGrid n) :
    (liftedPhaseCell Q n q i).card = (phaseCell n (fun x : Q ↦ q x) i).card :=
  card_image_of_injective _ Subtype.val_injective

lemma liftedPhaseCell_mean (Q : Finset G) (n : ℕ) (q : G → ℂ) (i : PhaseGrid n) (f : G → ℝ) :
    (𝔼 x : liftedPhaseCell Q n q i, f x) = 𝔼 x : phaseCell n (fun y : Q ↦ q y) i, f x := by
  rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,
    Fintype.card_coe,Fintype.card_coe,liftedPhaseCell_card]
  congr 1
  rw [sum_coe_sort (liftedPhaseCell Q n q i) f,
    sum_coe_sort (phaseCell n (fun y : Q ↦ q y) i) (fun y : Q ↦ f y)]
  exact sum_image (fun x _ y _ h ↦ Subtype.val_injective h)

/-- Averaged normalized correlation on Q yields a phase cell occupying a
polynomial fraction of Q, and a polynomial positive density increase. -/
theorem normalized_phase_density_increment (Q : Finset G) (hQ : Q.Nonempty)
    (A : Finset G) (q : G → G → ℂ) (hq : ∀ a x, ‖q a x‖ ≤ 1)
    {r : ℝ} (hr : 0 < r)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 y : Q,
      (((indicator A (a+y)-density A : ℝ) : ℂ))*conj (q a y)‖^2) :
    ∃ a : G, ∃ S : Finset G, IsInteriorPhaseCell (phaseResolution r) Q (q a) S ∧
      S.Nonempty ∧ r^3/2048*(Q.card : ℝ) ≤ (S.card : ℝ) ∧
      density A+r/16 ≤ ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  letI : Nonempty Q := hQ.to_subtype
  let f : G → Q → ℝ := fun a y ↦ indicator A (a+y)-density A
  have hf (a : G) (y : Q) : |f a y| ≤ 1 := centered_indicator_bound A _
  have hf0 : (𝔼 a, 𝔼 y : Q, f a y) = 0 := by
    rw [expect_comm]
    have hz (y : Q) : (𝔼 a, f a y) = 0 := by
      simp only [f,expect_sub_distrib,Fintype.expect_const]
      have hh : (𝔼 a : G, indicator A (a+y)) = density A :=
        (Fintype.expect_equiv (Equiv.addRight (y : G)) _ (indicator A) (fun _ ↦ rfl)).trans (expect_indicator A)
      rw [hh,sub_self]
    simp only [hz,Fintype.expect_const]
  obtain ⟨a,i,hJ,hcard,hinc⟩ := averaged_normalized_phase_increment f
    (fun a (y : Q) ↦ q a y) hf hf0 (fun a (y : Q) ↦ hq a y) hr hcorr
  let S := liftedPhaseCell Q (phaseResolution r) (q a) i
  have hS : S.Nonempty := image_nonempty.mpr hJ
  letI : Nonempty S := hS.to_subtype
  have hmean : r/16 ≤ 𝔼 x : S, (indicator A (a+x)-density A) := by
    rw [liftedPhaseCell_mean Q (phaseResolution r) (q a) i (fun x ↦ indicator A (a+x)-density A)]
    exact hinc
  rw [expect_sub_distrib,Fintype.expect_const,indicator_cell_mean] at hmean
  refine ⟨a,S,liftedPhaseCell_shape _ _ _ _,hS,?_,by linarith⟩
  simpa only [S,liftedPhaseCell_card,Fintype.card_coe] using hcard

/-- Large U³ gives a quadratic phase-cell increment with polynomial relative
size and polynomial gain. Rank is independent of the ambient group size. -/
theorem normalized_quadratic_density_increment
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (A : Finset G)
    {δ r : ℝ} (hδ : 0 < δ)
    (hU : δ ≤ uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)))
    (hr : 0 < r) (hrcorr : r ≤ normalizedCorrelation δ) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → ℂ, ∃ a : G, ∃ S : Finset G,
      C.card ≤ normalizedRank δ ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (bohr C (1/16) : Set G) q ∧
      IsInteriorPhaseCell (phaseResolution r) (bohr C (1/16)) q S ∧ S.Nonempty ∧
      r^3/2048*((bohr C (1/16)).card : ℝ) ≤ (S.card : ℝ) ∧
      density A+r/16 ≤ ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  have hf (x : G) : ‖((indicator A x-density A : ℝ) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using centered_indicator_bound A x
  obtain ⟨C,q,hC,hq,hquad,hcorr⟩ := normalized_local_quadratic_inverse h2 _ hf hδ hU
  have hQ : (bohr C (1/16)).Nonempty := ⟨0,bohr_zero C (by norm_num)⟩
  obtain ⟨a,S,hcell,hS,hcard,hinc⟩ := normalized_phase_density_increment (bohr C (1/16)) hQ A q
    (fun a x ↦ (hq a x).le) hr (hrcorr.trans hcorr)
  exact ⟨C,q a,a,S,hC,hq a,hquad a,hcell,hS,hcard,hinc⟩

#print axioms normalized_quadratic_density_increment
end Erdos3NormalizedQuadraticDensityIncrement
