import Submission.InteriorBohrBiasTransfer

/-! A biased local quadratic phase admits a bounded-rank translated
flattening refinement with all windows constructed. No derivative-character
representation is assumed. The window hierarchy is independent of the phase. -/
namespace Erdos3UnconditionalBiasedPhaseRefinement
open Finset Erdos3InteriorBohrBiasTransfer Erdos3BiasedQuadraticBohrRefinement
  Erdos3BohrDerivativeCharacters Erdos3LocalQuadraticInverse Erdos3FiniteUniformity
  Erdos3FiniteFourier Erdos3CorrelationSifting Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3RelativeStableBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

structure RefinementGeometry (D : Finset (AddChar G ℂ)) (R : ℝ)
    (o v z w : ℕ) (u r s : ℝ) : Prop where
  u_lower : relativeWidth D o R/8 ≤ u
  u_upper : u ≤ relativeWidth D o R/4
  u_stable : RelativeStable D v u
  r_lower : relativeWidth D v u/4 ≤ r
  r_upper : r ≤ relativeWidth D v u/2
  r_stable : RelativeStable D z r
  s_lower : relativeWidth D z r/4 ≤ s
  s_upper : s ≤ relativeWidth D z r/2
  s_stable : RelativeStable D w s

/-- The initial bias is transferred from the original stable domain to an
interior translate of the constructed inner window. Both lost boundary
fractions and all later approximation errors remain in the statement. -/
theorem exists_unconditional_biased_refinement (D : Finset (AddChar G ℂ))
    {R : ℝ} (hR : 0 < R) {o v z w : ℕ}
    (ho : 0 < o) (hv : 0 < v) (hz : 0 < z) (hw : 0 < w)
    (hst : RelativeStable D o R) {ρ β η ε : ℝ}
    (hρ : 0 < ρ) (hsize : ρ^2 ≤ density (bohr D (relativeWidth D o R/8)))
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1) (herr : ε ≤ η^2/2)
    (hβ : 1/(z : ℝ) < β-2/(o : ℝ))
    (hbudget : η ≤ β-2/(o : ℝ)-1/((v : ℝ)*ρ)-1/(z : ℝ)) :
    ∃ u r s : ℝ, RefinementGeometry D R o v z w u r s ∧
      ∀ q : G → ℂ, (∀ x, ‖q x‖ = 1) →
        IsLocallyQuadratic (bohr D R : Set G) q → β ≤ ‖𝔼 x : bohr D R, q x‖ →
        ∃ E : Finset (AddChar G ℂ), (E.card : ℝ) ≤ 2/η^2 ∧
          ((D ∪ E).card : ℝ) ≤ D.card+2/η^2 ∧
          ∀ t : ℝ, 0 ≤ t → t ≤ r → t ≤ relativeWidth D z r →
            t ≤ relativeWidth D w s → r+s+t ≤ relativeWidth D o R →
            ∃ b ∈ bohr D R,
              (∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, (b+x)+y ∈ bohr D R) ∧
              (∀ y ∈ bohr (D ∪ E) t, ‖q (b+y)-q b‖ ≤
                refinementError (1/((v : ℝ)*ρ)) (β-2/(o : ℝ)) ε z w t) ∧
              ∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t,
                ‖q ((b+x)+y)-q (b+x)‖ ≤ 1/((v : ℝ)*ρ)+1/(z : ℝ)/ε+t+
                  refinementError (1/((v : ℝ)*ρ)) (β-2/(o : ℝ)) ε z w t := by
  let U := relativeWidth D o R
  have hU : 0 < U := relativeWidth_pos D ho hR
  obtain ⟨u,hu₁,hu₂,hust,hchars⟩ := exists_stable_derivative_characters D hU hv hρ hsize
  have hu : 0 < u := (show 0 < U/8 by positivity).trans_le hu₁
  have hV : 0 < relativeWidth D v u := relativeWidth_pos D hv hu
  obtain ⟨r,hr₁,hr₂,hrst⟩ := exists_relative_stable D (show 0 < relativeWidth D v u/4 by positivity) hz
  have hr : 0 < r := (show 0 < relativeWidth D v u/4 by positivity).trans_le hr₁
  have hr₂' : r ≤ relativeWidth D v u/2 := by linarith
  have hZ : 0 < relativeWidth D z r := relativeWidth_pos D hz hr
  obtain ⟨s,hs₁,hs₂,hsst⟩ := exists_relative_stable D (show 0 < relativeWidth D z r/4 by positivity) hw
  have hs : 0 < s := (show 0 < relativeWidth D z r/4 by positivity).trans_le hs₁
  have hs₂' : s ≤ relativeWidth D z r/2 := by linarith
  have hvr := relativeWidth_le_quarter D hv hu.le
  have hzr := relativeWidth_le_quarter D hz hr.le
  have hrU : r ≤ U := by linarith
  have hsU : s ≤ U/4 := by linarith
  refine ⟨u,r,s,⟨hu₁,hu₂,hust,hr₁,hr₂',hrst,hs₁,hs₂',hsst⟩,?_⟩
  intro q hq hquad hbias
  obtain ⟨a,ha,hqa,hquada,hba⟩ := exists_interior_bohr_bias D hR ho hst
    (bohr D r) ⟨0,bohr_zero D hr.le⟩ (bohr_mono D hrU) q hq hquad hbias
  obtain ⟨F,hF⟩ := hchars (fun x ↦ q (a+x)) hqa hquada
  have happ : ∀ h ∈ bohr D s, ∀ x ∈ bohr D r,
      ‖derivative (fun x ↦ q (a+x)) h x-
        derivative (fun x ↦ q (a+x)) h 0*F h x‖ ≤ 1/((v : ℝ)*ρ) := by
    intro h hh x hx
    exact hF h (bohr_mono D hsU hh) x (bohr_mono D (by linarith : r ≤ relativeWidth D v u) hx)
  obtain ⟨E,hE,hDE,hflat⟩ := exists_biased_quadratic_refinement D hr hs hz hw hrst hsst
    (by linarith : s ≤ relativeWidth D z r) (fun x ↦ q (a+x)) hqa hquada F
    hη hε hε1 herr hβ hbudget hba happ
  refine ⟨E,hE,hDE,?_⟩
  intro t ht htr htz htw hsum
  obtain ⟨b,hb,hbase,hall⟩ := hflat t ht htr htz htw hsum
  refine ⟨a+b,?_,?_,?_,?_⟩
  · have hbU := bohr_mono D hrU hb
    simpa only [U,sub_add_cancel] using bohr_add ha hbU
  · intro x hx y hy
    have hyD : y ∈ bohr D t := mem_bohr.mpr
      (fun χ hχ ↦ mem_bohr.mp hy χ (mem_union_left _ hχ))
    exact bohr_mono D (by linarith)
      (bohr_add (bohr_add (bohr_add ha hb) hx) hyD)
  · intro y hy
    simpa only [add_assoc] using hbase y hy
  · intro x hx y hy
    simpa only [add_assoc] using hall x hx y hy

#print axioms exists_unconditional_biased_refinement
end Erdos3UnconditionalBiasedPhaseRefinement
