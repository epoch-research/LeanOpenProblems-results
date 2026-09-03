import Submission.GeometricPrimeBlockBands
import Submission.SharpConicCharacterBandSource

/-!
Geometrically budgeted score bounds for rationally proportional conic roots.
This includes integer dilations and common-factor normalizations. It is a
positive-density source theorem, not a Sidon construction.
-/
namespace Erdos1206.ProportionalConicBandSource
open Finset PrimeBlockVariance MovingPrimeBlockVariance SharpPrimeBlockVariance
open SquarefreeConicFamily SquarefreeConicCharacterScore ConicCharacterBandSource
open ConicPrimeCharacterScore
open scoped Classical

/-- Completely additive contrasts are unchanged by positive rational scaling,
expressed without division. -/
lemma contrast_proportional (P : Finset ℕ) (w : ℕ → ℤ)
    (x y : Fin 4 → ℕ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hprop : ∀ i, x i*y 0=x 0*y i) :
    contrast P w (x 0) (x 1) (x 2) (x 3) =
      contrast P w (y 0) (y 1) (y 2) (y 3) := by
  have hh (i : Fin 4) : y 0*x i=x 0*y i := by simpa only [mul_comm] using hprop i
  calc
    _ = contrast P w (y 0*x 0) (y 0*x 1) (y 0*x 2) (y 0*x 3) :=
      (contrast_dilation P w (hx 0) (hx 1) (hx 2) (hx 3) (hy 0)).symm
    _ = contrast P w (x 0*y 0) (x 0*y 1) (x 0*y 2) (x 0*y 3) := by
      rw [hh 0,hh 1,hh 2,hh 3]
    _ = _ := contrast_dilation P w (hy 0) (hy 1) (hy 2) (hy 3) (hx 0)

lemma proportional_order (x : Fin 4 → ℕ) {t u : ℕ}
    (hu : 0 < u) (hx : 0 < x 0)
    (hprop : ∀ i, x i*F 0 t u=x 0*F i t u) :
    (∀ i, 0 < x i) ∧ x 0 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3 ∧
      x 3 ≤ 1000000*x 0 := by
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered t u hu
  have hy (i : Fin 4) : 0 < F i t u := by
    fin_cases i
    · exact ha
    · exact ha.trans hab
    · exact ha.trans (hab.trans hbc)
    · exact ha.trans (hab.trans (hbc.trans hcd))
  have hxall (i : Fin 4) : 0 < x i := by
    have hh : 0 < x i*F 0 t u := by rw [hprop]; exact Nat.mul_pos hx (hy i)
    exact Nat.pos_of_mul_pos_right hh
  have hlt (i k : Fin 4) (hik : F i t u < F k t u) : x i < x k := by
    have hh : x i*F 0 t u < x k*F 0 t u := by
      rw [hprop,hprop]
      exact Nat.mul_lt_mul_of_pos_left hik hx
    exact (Nat.mul_lt_mul_right ha).mp hh
  refine ⟨hxall,hlt 0 1 hab,hlt 1 2 hbc,hlt 2 3 hcd,?_⟩
  apply fun hh => Nat.le_of_mul_le_mul_right hh ha
  rw [hprop]
  have hh := Nat.mul_le_mul_left (x 0) (root_ratio t u)
  simpa only [mul_assoc,mul_left_comm] using hh

lemma family_contrast_proportional (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 1000000000 < p)
    (x : Fin 4 → ℕ) {t u : ℕ} (hcop : Nat.Coprime t u)
    (hu : 0 < u) (hx : 0 < x 0)
    (hprop : ∀ i, x i*F 0 t u=x 0*F i t u) :
    contrast P (fun p => χ p-ψ p) (x 0) (x 1) (x 2) (x 3) =
      2*(mixedMass P χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℤ) := by
  have hxall := (proportional_order x hu hx hprop).1
  have hy : ∀ i, 0 < F i t u := by
    intro i
    have hh : 0 < x 0*F i t u := by
      rw [←hprop]
      exact Nat.mul_pos (hxall i) (ordered t u hu).1
    exact Nat.pos_of_mul_pos_left hh
  rw [contrast_proportional P _ x (fun i => F i t u) hxall hy hprop]
  simpa only [one_mul] using family_contrast P hP hcop hu (by decide : 0 < (1:ℕ))

/-- One source constant works for all prime blocks. The conclusion applies to
all positive rational scalings of primitive-parameter conic points. -/
theorem exists_source (b : ℝ) (hb : 1 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℕ → Finset ℕ,
      (∀ j p, p ∈ P j → p.Prime ∧ 1000000000 < p) →
      ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
        ∀ (j t u : ℕ) (x : Fin 4 → ℕ), Nat.Coprime t u → 0 < u → 0 < x 0 →
          (∀ i, x i*F 0 t u=x 0*F i t u) → (∀ i, x i ∈ A) →
          (mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℝ) ≤
            4*Real.sqrt (K*b^j*mass (P j) weight)+2*Real.sqrt (2000000*mass (P j) weight) := by
  obtain ⟨K,hK,hbands⟩ := GeometricPrimeBlockBands.exists_squarefree_good_bands b hb
  refine ⟨K,hK,fun P hP => ?_⟩
  obtain ⟨A,hAS,hAd,hband⟩ := hbands P (fun _ => weight)
    (fun j p hp => (hP j p hp).1)
  refine ⟨A,hAS,hAd,fun j t u x hcop hu hx hprop hmem => ?_⟩
  obtain ⟨hxall,hab,hbc,hcd,hratio⟩ := proportional_order x hu hx hprop
  have hscale := family_contrast_proportional (P j) (hP j) x hcop hu hx hprop
  have hscaleR : (contrast (P j) (fun p => χ p-ψ p)
      (x 0) (x 1) (x 2) (x 3):ℝ) =
      2*(mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℝ) := by
    exact_mod_cast hscale
  have hscore (i : Fin 4) : (score (P j) (fun p => χ p-ψ p) (x i):ℝ) =
      2*primeSum (P j) weight (x i) :=
    squarefree_score (P j) _ (fun p hp => (hP j p hp).1) (hAS _ (hmem i))
  simp only [contrast,Int.cast_add,Int.cast_sub,hscore] at hscaleR
  have hbd := SharpConicCharacterBandSource.band_contrast_bound (P j) weight
    (fun p hp => (hP j p hp).1) hx hab.le hbc.le hcd.le hratio
    (by decide : 1 ≤ (1000000:ℕ))
    (mul_nonneg (mul_nonneg hK.le (pow_nonneg (zero_lt_one.trans hb).le j)) (mass_nonneg _ _))
    (hband _ (hmem 0) j) (hband _ (hmem 1) j) (hband _ (hmem 2) j) (hband _ (hmem 3) j)
  norm_num only [Nat.cast_ofNat] at hbd
  linarith

#print axioms contrast_proportional
#print axioms proportional_order
#print axioms family_contrast_proportional
#print axioms exists_source
end Erdos1206.ProportionalConicBandSource
