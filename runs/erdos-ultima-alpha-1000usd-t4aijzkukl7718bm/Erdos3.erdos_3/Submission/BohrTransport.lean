import Submission.DoubledWeights

/-! Bohr sets transported through additive equivalences, including doubling. -/
namespace Erdos3BohrTransport
open Finset Erdos3FiniteBohr Erdos3DoubledWeights
open scoped BigOperators Classical
set_option maxHeartbeats 1500000

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

noncomputable def transportChars (e : G ≃+ H) (D : Finset (AddChar G ℂ)) :
    Finset (AddChar H ℂ) := D.image (fun χ ↦ χ.compAddMonoidHom e.symm.toAddMonoidHom)

lemma char_transport_injective (e : G ≃+ H) :
    Function.Injective (fun χ : AddChar G ℂ ↦ χ.compAddMonoidHom e.symm.toAddMonoidHom) := by
  intro χ ψ h
  ext x
  have hh := congrArg (fun f : AddChar H ℂ ↦ f (e x)) h
  simpa using hh

lemma transportChars_card (e : G ≃+ H) (D : Finset (AddChar G ℂ)) :
    (transportChars e D).card = D.card := card_image_of_injective _ (char_transport_injective e)

lemma transport_bohr (e : G ≃+ H) (D : Finset (AddChar G ℂ)) (r : ℝ) :
    (bohr D r).image e = bohr (transportChars e D) r := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    apply mem_bohr.mpr
    intro ψ hψ
    obtain ⟨χ,hχ,rfl⟩ := mem_image.mp hψ
    simpa using mem_bohr.mp hx χ hχ
  · intro hy
    have hx : e.symm y ∈ bohr D r := by
      apply mem_bohr.mpr
      intro χ hχ
      have hh := mem_bohr.mp hy (χ.compAddMonoidHom e.symm.toAddMonoidHom)
        (mem_image.mpr ⟨χ,hχ,rfl⟩)
      simpa using hh
    exact mem_image.mpr ⟨e.symm y,hx,by simp⟩

lemma transport_bohr_card (e : G ≃+ H) (D : Finset (AddChar G ℂ)) (r : ℝ) :
    (bohr (transportChars e D) r).card = (bohr D r).card := by
  rw [← transport_bohr]
  exact card_image_of_injective _ e.injective

lemma transport_bohr_growth (e : G ≃+ H) (D : Finset (AddChar G ℂ))
    {r h δ : ℝ}
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ)) :
    ((bohr (transportChars e D) (r+h)).card : ℝ) ≤
      (1+δ)*((bohr (transportChars e D) (r-h)).card : ℝ) := by
  simpa only [transport_bohr_card] using hgrowth

lemma doubled_bohr_subset (h2 : Function.Bijective (fun x : G ↦ x+x))
    (D : Finset (AddChar G ℂ)) (r : ℝ) :
    bohr (transportChars (doublingEquiv G h2) D) r ⊆ bohr D (2*r) := by
  rw [← transport_bohr]
  intro y hy
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  simpa only [doublingEquiv_apply, two_mul] using bohr_add hx hx

lemma doubled_bohr_mass (h2 : Function.Bijective (fun x : G ↦ x+x))
    (D : Finset (AddChar G ℂ)) (r : ℝ) (hr : 0 ≤ r) (A U : Finset G) (x : G)
    (hsub : ∀ b ∈ bohr D r, ∀ c ∈ bohr D r, c-b ∈ U) :
    Erdos3LocalThreeAPMoment.doubledMass (window A U x)
      (Erdos3CorrelationMoments.corr
        (Erdos3CorrelationSifting.normalized (bohr (transportChars (doublingEquiv G h2) D) r))) =
      Erdos3PopularAlmostPeriods.diffSmooth (bohr D r) (Erdos3CorrelationSifting.indicator A) x := by
  rw [← transport_bohr]
  exact doubled_mass_window h2 A U (bohr D r) ⟨0,bohr_zero _ hr⟩ x hsub

#print axioms transport_bohr
#print axioms doubled_bohr_mass
end Erdos3BohrTransport
