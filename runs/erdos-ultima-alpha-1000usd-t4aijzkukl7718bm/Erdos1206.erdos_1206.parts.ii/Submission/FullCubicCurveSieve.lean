import Submission.AllNormalizationsFamilySieve

/-!
The full homogeneous cubic curve underlying the earlier narrow-congruence
collision family is avoidable at positive density, with arbitrary primitive
integer parameters, common-factor cancellation, and integer dilations.
This covers one rational curve, not the whole Fermat cubic surface.
-/
namespace Erdos1206.FullCubicCurveSieve
open MvPolynomial CertifiedBinaryFamilySieve NormalizedBinaryFamilySieve AllNormalizationsFamilySieve

noncomputable def cubic (a b c d : ℤ) : BinaryForm :=
  C a*X 0^3+C b*X 0^2*X 1+C c*X 0*X 1^2+C d*X 1^3

lemma cubic_homogeneous (a b c d : ℤ) : (cubic a b c d).IsHomogeneous 3 := by
  have hx := isHomogeneous_X ℤ (0:Fin 2)
  have hy := isHomogeneous_X ℤ (1:Fin 2)
  exact (((((isHomogeneous_C (Fin 2) a).mul (hx.pow 3)).add
    (((isHomogeneous_C (Fin 2) b).mul (hx.pow 2)).mul hy)).add
    (((isHomogeneous_C (Fin 2) c).mul hx).mul (hy.pow 2))).add
    ((isHomogeneous_C (Fin 2) d).mul (hy.pow 3)))

noncomputable def forms : Fin 4 → BinaryForm :=
  ![cubic 1 (-4) 12 (-63),cubic 1 (-1) 27 (-42),cubic 1 1 27 42,cubic 1 4 12 63]

lemma forms_homogeneous (i : Fin 4) : (forms i).IsHomogeneous 3 := by
  fin_cases i <;> apply cubic_homogeneous

/-- The full binary identity, not only a positive-cone specialization. -/
theorem cube_identity : forms 0^3+forms 3^3=forms 1^3+forms 2^3 := by
  dsimp [forms,cubic]
  norm_num
  ring

private noncomputable def cert₀ : Fin 4 → BinaryForm :=
  ![7*(145*X 0^2+654*X 0*X 1-1344*X 1^2),
    7*(5*X 0^2-69*X 0*X 1+2016*X 1^2),0,0]

private noncomputable def cert₁ : Fin 4 → BinaryForm :=
  ![-X 0^2+X 0*X 1-20*X 1^2,X 0^2-4*X 0*X 1+5*X 1^2,0,0]

lemma certificate₀ : ∑ i, cert₀ i*forms i=C (1050:ℤ)*X 0^5 := by
  rw [Fin.sum_univ_four]
  dsimp [cert₀,forms,cubic]
  norm_num
  ring

lemma certificate₁ : ∑ i, cert₁ i*forms i=C (1050:ℤ)*X 1^5 := by
  rw [Fin.sum_univ_four]
  dsimp [cert₁,forms,cubic]
  norm_num
  ring

/-- The common divisor of the four coordinates divides one fixed integer.
Thus large cancellation is handled, rather than silently discarded. -/
theorem cancellation_dvd {u v g : ℤ} (hcop : IsCoprime u v)
    (hg : ∀ i, g ∣ eval ![u,v] (forms i)) : g ∣ 1050 := by
  apply BinaryHomogeneousHeight.common_divisor_dvd_certificate
    (F := fun i => eval ![u,v] (forms i))
    (H := fun i => eval ![u,v] (cert₀ i)) (K := fun i => eval ![u,v] (cert₁ i)) hcop hg
  · have hh := congrArg (eval ![u,v]) certificate₀
    simpa using hh
  · have hh := congrArg (eval ![u,v]) certificate₁
    simpa using hh

/-- An unconditional positive-density avoider for every primitive rational
parameter of this cubic curve, every integral normalization, and every dilation.
The maximum-one exception cannot contain four distinct positive roots. -/
theorem full_cubic_family_avoidable :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ (p : ℤ × ℤ) (g t : ℕ), IsCoprime p.1 p.2 →
        (∀ i, (g:ℤ) ∣ eval ![p.1,p.2] (forms i)) →
        1 < rootHeight (normalized forms g p) →
        ∃ i : Fin 4, t*(normalized forms g p i).natAbs ∉ A := by
  obtain ⟨A,hA,hden,havoid⟩ := positive_density_avoids_all_normalizations
    (by decide : 0 < 4) (by decide : 3 ≤ 3) (by norm_num : (1050:ℤ) ≠ 0)
    forms_homogeneous certificate₀ certificate₁
  exact ⟨A,hA,hden,fun p g t hp hg hm => havoid p g t ⟨hp,hg,hm⟩⟩

#print axioms cube_identity
#print axioms cancellation_dvd
#print axioms full_cubic_family_avoidable
end Erdos1206.FullCubicCurveSieve
