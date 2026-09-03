import Submission.SignedLogarithmicPrimeBands
import Submission.ProportionalConicBandSource

/-!
The signed logarithmic band source applied to every rational normalization and
dilation of the explicit conic. This remains a familywise source constraint.
-/
namespace Erdos1206.LogarithmicConicBandSource
open Finset PrimeBlockVariance MovingPrimeBlockVariance SharpPrimeBlockVariance
open SquarefreeConicFamily SquarefreeConicCharacterScore ConicCharacterBandSource
open ConicPrimeCharacterScore ProportionalConicBandSource
open scoped Classical

/-- The source loss grows logarithmically in the prime-block index, rather
than geometrically. The conclusion includes arbitrary positive rational scaling. -/
theorem exists_source :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℕ → Finset ℕ,
      (∀ j p, p ∈ P j → p.Prime ∧ 1000000000 < p) →
      ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
        ∀ (j t u : ℕ) (x : Fin 4 → ℕ), Nat.Coprime t u → 0 < u → 0 < x 0 →
          (∀ i, x i*F 0 t u=x 0*F i t u) → (∀ i, x i ∈ A) →
          (mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℝ) ≤
            4*Real.sqrt (K*(Nat.log 2 (j+1)+1:ℕ)*(mass (P j) weight+(Nat.log 2 (j+1)+1:ℕ)))+2*Real.sqrt (2000000*mass (P j) weight) := by
  obtain ⟨K,hK,hbands⟩ := SignedLogarithmicPrimeBands.exists_signed_logarithmic_bands
    {n : ℕ | Squarefree n} squarefree_lowerDensity_pos
    (fun n hn => Nat.pos_of_ne_zero hn.ne_zero)
  refine ⟨K,hK,fun P hP => ?_⟩
  obtain ⟨A,hAS,hAd,hband⟩ := hbands P (fun _ => weight)
    (fun j p hp => (hP j p hp).1)
    (fun j p hp => weight_bound (hP j p hp).1 (hP j p hp).2)
  refine ⟨A,hAS,hAd,fun j t u x hcop hu hx hprop hmem => ?_⟩
  obtain ⟨hxall,hab,hbc,hcd,hratio⟩ := proportional_order x hu hx hprop
  have hscale := family_contrast_proportional (P j) (hP j) x hcop hu hx hprop
  have hscaleR : (contrast (P j) (fun p => χ p-ψ p)
      (x 0) (x 1) (x 2) (x 3):ℝ) =
      2*(mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℝ) := by
    exact_mod_cast hscale
  have hscore (i : Fin 4) : (score (P j) (fun p => χ p-ψ p) (x i):ℝ) =
      2*primeSum (P j) weight (x i) :=
    squarefree_score (P j) _ (fun p hp => (hP j p hp).1) (hAS (hmem i))
  simp only [contrast,Int.cast_add,Int.cast_sub,hscore] at hscaleR
  have hbd := SharpConicCharacterBandSource.band_contrast_bound (P j) weight
    (fun p hp => (hP j p hp).1) hx hab.le hbc.le hcd.le hratio
    (by decide : 1 ≤ (1000000:ℕ))
    (show 0 ≤ K*(Nat.log 2 (j+1)+1:ℕ)*(mass (P j) weight+(Nat.log 2 (j+1)+1:ℕ)) by
      have := mass_nonneg (P j) weight
      positivity)
    (hband _ (hmem 0) j) (hband _ (hmem 1) j) (hband _ (hmem 2) j) (hband _ (hmem 3) j)
  norm_num only [Nat.cast_ofNat] at hbd
  linarith


#print axioms exists_source
end Erdos1206.LogarithmicConicBandSource
