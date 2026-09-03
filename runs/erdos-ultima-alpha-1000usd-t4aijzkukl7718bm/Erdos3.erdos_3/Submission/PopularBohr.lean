import Submission.FourierSmoothing
import Submission.SpectralAlmostPeriods

/-! Popular-difference concentration on a quantitative Bohr set.
This is still an auxiliary result, not a proof of Erdős Problem 3. -/
namespace Erdos3PopularBohr
open Finset Erdos3CorrelationSifting Erdos3PopularAlmostPeriods Erdos3FiniteFourier
  Erdos3FourierSmoothing Erdos3SpectralAlmostPeriods Erdos3FiniteBohr
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Starting from a sifted set B, popular differences remain concentrated after every
shift in a Bohr set. The rank, packing cost, and approximation error are explicit. -/
theorem exists_popular_bohr (B S : Finset G) (hB : B.Nonempty) (hS : S.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {δ η : ℝ} (hη : 0 ≤ η)
    (hbad : pairDensity B (fun x ↦ 1-f x) ≤ δ*(density B)^2)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (n : ℕ)
    (hBd : Fintype.card G ≤ 2^(2*m)*B.card) :
    ∃ T : Finset G, T.Nonempty ∧ T ⊆ S ∧
      B.card^(256*m^4*r^2)*S.card ≤ 2*(B+S).card^(256*m^4*r^2)*T.card ∧
      ∃ D : Finset (AddChar G ℂ),
        D.card ≤ ⌊16*Real.log (1/density T)⌋₊ ∧
        (∀ t ∈ bohr D (η/(D.card+1)), ∀ x : G,
          |diffSmooth B f (x+t)-diffSmooth B f x| ≤
            4*(n : ℝ)/(r : ℝ)+(1/density B)*(η+2*(1/2 : ℝ)^(2*n))) ∧
        ∀ t ∈ bohr D (η/(D.card+1)),
          1-δ-(4*(n : ℝ)/(r : ℝ)+(1/density B)*(η+2*(1/2 : ℝ)^(2*n))) ≤
            diffSmooth B f t := by
  obtain ⟨T,hT,hTS,hcard,hper,_⟩ := exists_popular_almost_periods B S hB hS f hf hbad hm hr hBd
  let g : G → ℂ := fun x ↦ (diffSmooth B f x : ℂ)
  have hg : (∑ χ : AddChar G ℂ, ‖hat g χ‖) ≤ 1/density B := by
    have hh := cdiffSmooth_hat_l1 B hB (fun x ↦ (f x : ℂ)) (fun x ↦ by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf x).1] using (hf x).2)
    have he : cdiffSmooth B (fun x ↦ (f x : ℂ)) = g := funext (cdiffSmooth_ofReal B f)
    rw [he] at hh
    exact hh
  have hgper : ∀ s ∈ T, ∀ t ∈ T, ∀ x, ‖g (x+s-t)-g x‖ ≤ 2/(r : ℝ) := by
    intro s hs t ht x
    have hh := hper s hs t ht (x-t)
    have he : x-t+s = x+s-t := by abel
    rw [he, sub_add_cancel] at hh
    simpa only [g, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh
  obtain ⟨D,_,hD,hbper⟩ := exists_bohr_almost_periods T hT g n hg hη hgper
  have herror : 2*(n : ℝ)*(2/(r : ℝ)) = 4*(n : ℝ)/(r : ℝ) := by ring
  rw [herror] at hbper
  have hrper : ∀ t ∈ bohr D (η/(D.card+1)), ∀ x : G,
      |diffSmooth B f (x+t)-diffSmooth B f x| ≤
        4*(n : ℝ)/(r : ℝ)+(1/density B)*(η+2*(1/2 : ℝ)^(2*n)) := by
    simpa only [g, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbper
  refine ⟨T,hT,hTS,hcard,D,hD,hrper,?_⟩
  intro t ht
  have hh := hrper t ht 0
  rw [zero_add] at hh
  have h0 := diffSmooth_zero_lower B hB f hbad
  have hl := (abs_le.mp hh).1
  linarith

#print axioms exists_popular_bohr
end Erdos3PopularBohr
