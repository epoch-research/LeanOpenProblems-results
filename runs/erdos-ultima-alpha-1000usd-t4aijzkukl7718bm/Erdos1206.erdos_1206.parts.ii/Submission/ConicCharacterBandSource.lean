import Submission.PrimeBlockBandDensity
import Submission.PrimeBlockMeanOscillation
import Submission.SquarefreeConicCharacterScore

/-!
A positive-density squarefree source whose surviving dilated instances of the
explicit conic family have quantitatively small mixed-prime mass in every
prescribed prime block. This does not assert that no such instances survive.
-/
namespace Erdos1206.ConicCharacterBandSource
open Finset PrimeBlockVariance MovingPrimeBlockVariance PrimeBlockBandDensity
open PrimeBlockMeanOscillation SquarefreeConicFamily SquarefreeConicCharacterScore
open ConicPrimeCharacterScore
open scoped Classical

noncomputable def weight (p : ℕ) : ℝ := ((χ p-ψ p:ℤ):ℝ)/2

lemma weight_bound {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) : |weight p| ≤ 1 := by
  obtain ⟨hx,hy⟩ := symbols hp hbig
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> norm_num [weight,hx,hy]

lemma squarefree_score (P : Finset ℕ) (z : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : Squarefree n) :
    (score P z n:ℝ) = 2*primeSum P (fun p => (z p:ℝ)/2) n := by
  simp only [score,Int.cast_sum,Int.cast_mul,Int.cast_natCast,primeSum,mul_sum]
  apply sum_congr rfl
  intro p hp
  by_cases hd : p ∣ n
  · rw [Nat.factorization_eq_one_of_squarefree hn (hP p hp) hd]
    simp [indicator,hd]
    ring
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    simp [indicator,hd]

lemma root_ratio (t u : ℕ) : F 3 t u ≤ 1000000*F 0 t u := by
  dsimp [F,QuadraticSquarefreeSieve.quad,a,b,c]
  ring_nf
  omega

lemma band_contrast_bound (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, |w p| ≤ 1)
    {a b c d R : ℕ} {B : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hda : d ≤ R*a) (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hA : (primeSum P w a-movingMean P w a)^2 ≤ B)
    (hB' : (primeSum P w b-movingMean P w b)^2 ≤ B)
    (hC : (primeSum P w c-movingMean P w c)^2 ≤ B)
    (hD : (primeSum P w d-movingMean P w d)^2 ≤ B) :
    primeSum P w a+primeSum P w b-primeSum P w c-primeSum P w d ≤
      4*Real.sqrt B+4*(R:ℝ) := by
  have hroot : Real.sqrt B^2=B := Real.sq_sqrt hB
  have hroot0 := Real.sqrt_nonneg B
  have hAb : |primeSum P w a-movingMean P w a| ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (abs_nonneg _) hroot0).mp
    simpa only [sq_abs,hroot] using hA
  have hBb : |primeSum P w b-movingMean P w b| ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (abs_nonneg _) hroot0).mp
    simpa only [sq_abs,hroot] using hB'
  have hCb : |primeSum P w c-movingMean P w c| ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (abs_nonneg _) hroot0).mp
    simpa only [sq_abs,hroot] using hC
  have hDb : |primeSum P w d-movingMean P w d| ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (abs_nonneg _) hroot0).mp
    simpa only [sq_abs,hroot] using hD
  have hac : c ≤ R*a := hcd.trans hda
  have hdb : d ≤ R*b := hda.trans (Nat.mul_le_mul_left R hab)
  have hmac := movingMean_oscillation P w hP hw ha (hab.trans hbc) hac hR
  have hmbd := movingMean_oscillation P w hP hw (ha.trans_le hab) (hbc.trans hcd) hdb hR
  obtain ⟨haL,haU⟩ := abs_le.mp hAb
  obtain ⟨hbL,hbU⟩ := abs_le.mp hBb
  obtain ⟨hcL,hcU⟩ := abs_le.mp hCb
  obtain ⟨hdL,hdU⟩ := abs_le.mp hDb
  have hmacL := (abs_le.mp hmac).1
  have hmbdL := (abs_le.mp hmbd).1
  linarith

/-- K is independent of every prime block. The source has positive LOWER
natural density, and the conclusion is uniform in the common dilation v. -/
theorem exists_source :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℕ → Finset ℕ,
      (∀ j p, p ∈ P j → p.Prime ∧ 1000000000 < p) →
      ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
        ∀ j t u v : ℕ, Nat.Coprime t u → 0 < u → 0 < v →
          (∀ i : Fin 4, v*F i t u ∈ A) →
          (mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℝ) ≤
            4*Real.sqrt (K*2^j*energy (P j) weight)+4000000 := by
  obtain ⟨K,hK,hbands⟩ := exists_squarefree_good_bands
  refine ⟨K,hK,fun P hP => ?_⟩
  obtain ⟨A,hAS,hAd,hband⟩ := hbands P (fun _ => weight)
    (fun j p hp => (hP j p hp).1)
    (fun j p hp => weight_bound (hP j p hp).1 (hP j p hp).2)
  refine ⟨A,hAS,hAd,fun j t u v hcop hu hv hmem => ?_⟩
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered t u hu
  have hscale := family_contrast (P j) (hP j) hcop hu hv
  have hscaleR : (contrast (P j) (fun p => χ p-ψ p)
      (v*F 0 t u) (v*F 1 t u) (v*F 2 t u) (v*F 3 t u):ℝ) =
      2*(mixedMass (P j) χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u):ℝ) := by
    exact_mod_cast hscale
  have hscore (i : Fin 4) : (score (P j) (fun p => χ p-ψ p) (v*F i t u):ℝ) =
      2*primeSum (P j) weight (v*F i t u) :=
    squarefree_score (P j) _ (fun p hp => (hP j p hp).1) (hAS _ (hmem i))
  simp only [contrast,Int.cast_add,Int.cast_sub,hscore] at hscaleR
  have hratio : v*F 3 t u ≤ 1000000*(v*F 0 t u) := by
    simpa only [mul_assoc,mul_left_comm] using Nat.mul_le_mul_left v (root_ratio t u)
  have hb := band_contrast_bound (P j) weight (fun p hp => (hP j p hp).1)
    (fun p hp => weight_bound (hP j p hp).1 (hP j p hp).2)
    (Nat.mul_pos hv ha) (Nat.mul_le_mul_left v hab.le) (Nat.mul_le_mul_left v hbc.le)
    (Nat.mul_le_mul_left v hcd.le) hratio (by decide : 1 ≤ (1000000:ℕ))
    (mul_nonneg (mul_nonneg hK.le (pow_nonneg (by norm_num) j)) (energy_pos _ _).le)
    (hband _ (hmem 0) j) (hband _ (hmem 1) j) (hband _ (hmem 2) j) (hband _ (hmem 3) j)
  norm_num only [Nat.cast_ofNat] at hb
  linarith

#print axioms squarefree_score
#print axioms band_contrast_bound
#print axioms exists_source
end Erdos1206.ConicCharacterBandSource
