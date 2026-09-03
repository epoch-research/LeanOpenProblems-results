import Submission.FullCubicCurveSieve

/-! The close-root cubic curve used in GeometricBandObstruction is avoidable
at positive lower density, including all primitive rational parameters,
common-factor normalizations, and integer dilations. This is a single-curve
result and does not settle the original conjecture. -/
namespace Erdos1206.DiagonalCubicCurveSieve
open MvPolynomial CertifiedBinaryFamilySieve NormalizedBinaryFamilySieve
  AllNormalizationsFamilySieve FullCubicCurveSieve

noncomputable def forms : Fin 4 → BinaryForm :=
  ![cubic 1 (-2) 0 (-3),cubic 1 (-1) 3 0,cubic 1 1 3 0,cubic 1 2 0 3]

lemma forms_homogeneous (i : Fin 4) : (forms i).IsHomogeneous 3 := by
  fin_cases i <;> apply cubic_homogeneous

lemma cube_identity : forms 0^3+forms 3^3=forms 1^3+forms 2^3 := by
  dsimp [forms,cubic]
  norm_num
  ring

private noncomputable def cert₀ : Fin 4 → BinaryForm :=
  ![3*(2*X 0^2+3*X 0*X 1),3*(2*X 0^2+3*X 0*X 1+3*X 1^2),0,0]

private noncomputable def cert₁ : Fin 4 → BinaryForm :=
  ![-X 0^2+2*X 0*X 1-4*X 1^2,X 0^2-3*X 0*X 1+2*X 1^2,0,0]

lemma certificate₀ : ∑ i, cert₀ i*forms i=C (12:ℤ)*X 0^5 := by
  rw [Fin.sum_univ_four]
  dsimp [cert₀,forms,cubic]
  norm_num
  ring

lemma certificate₁ : ∑ i, cert₁ i*forms i=C (12:ℤ)*X 1^5 := by
  rw [Fin.sum_univ_four]
  dsimp [cert₁,forms,cubic]
  norm_num
  ring

/-- Common-factor cancellation is uniformly bounded on the primitive
parameters of this curve. It is not being discarded without proof. -/
theorem cancellation_dvd {u v g : ℤ} (hcop : IsCoprime u v)
    (hg : ∀ i, g ∣ eval ![u,v] (forms i)) : g ∣ 12 := by
  apply BinaryHomogeneousHeight.common_divisor_dvd_certificate
    (F := fun i => eval ![u,v] (forms i))
    (H := fun i => eval ![u,v] (cert₀ i)) (K := fun i => eval ![u,v] (cert₁ i)) hcop hg
  · have hh := congrArg (eval ![u,v]) certificate₀
    simpa using hh
  · have hh := congrArg (eval ![u,v]) certificate₁
    simpa using hh

/-- The close-root family is sparse enough for a summable divisor sieve,
even after every allowed common-factor normalization and dilation. -/
theorem curve_avoidable :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      ∀ (p : ℤ × ℤ) (g t : ℕ), IsCoprime p.1 p.2 →
        (∀ i, (g:ℤ) ∣ eval ![p.1,p.2] (forms i)) →
        1<rootHeight (normalized forms g p) →
        ∃ i : Fin 4, t*(normalized forms g p i).natAbs ∉ A := by
  obtain ⟨A,hA,hden,havoid⟩ := positive_density_avoids_all_normalizations
    (by decide : 0<4) (by decide : 3≤3) (by norm_num : (12:ℤ)≠0)
    forms_homogeneous certificate₀ certificate₁
  exact ⟨A,hA,hden,fun p g t hp hg hm => havoid p g t ⟨hp,hg,hm⟩⟩

/-- This is exactly the polynomial family used for the relative-interval
collisions, not a different cubic curve. -/
lemma shifted_specialization (k : ℕ) :
    (fun i => eval ![(k:ℤ)+3,1] (forms i)) =
      ![(k:ℤ)^3+7*k^2+15*k+6,(k:ℤ)^3+8*k^2+24*k+27,
        (k:ℤ)^3+10*k^2+36*k+45,(k:ℤ)^3+11*k^2+39*k+48] := by
  funext i
  fin_cases i <;> simp [forms,cubic] <;> ring

#print axioms cube_identity
#print axioms cancellation_dvd
#print axioms curve_avoidable
#print axioms shifted_specialization
end Erdos1206.DiagonalCubicCurveSieve
