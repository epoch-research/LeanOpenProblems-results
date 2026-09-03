import Submission.JointQuadraticConeAnisotropy

/-! The formal cone algebra is identified with the two-equation quotient.
Consequently ideal membership of a sum of four fourth powers implies
coordinatewise ideal membership, with no degree restriction. -/
namespace Erdos322Research.JointQuadraticCone

noncomputable section
open MvPolynomial QuadraticSpecializationAnisotropy QuarticFormalSpecialization
set_option Elab.async false
set_option maxHeartbeats 0

abbrev Source := MvPolynomial (Fin 5) K

private def tailIndex (j : Fin 3) : Fin 5 := ⟨j.val+2,by omega⟩

def tailEmbed : Base →+* Source := MvPolynomial.eval₂Hom MvPolynomial.C
  (fun j ↦ MvPolynomial.X (tailIndex j))

def equation₀ : Source := X 0^2-tailEmbed radicand₀
def equation₁ : Source := X 1^2-tailEmbed radicand₁
def coneIdeal : Ideal Source := Ideal.span {equation₀,equation₁}

abbrev ConeQuotient := Source ⧸ coneIdeal

private def baseMap : Base →+* ConeRing :=
  (algebraMap FirstRoot ConeRing).comp (algebraMap Base FirstRoot)

private def coords : Fin 5 → ConeRing :=
  ![QuadraticAlgebra.omega,
    algebraMap FirstRoot ConeRing QuadraticAlgebra.omega,
    baseMap (X 0),baseMap (X 1),baseMap (X 2)]

def coneEval : Source →+* ConeRing :=
  MvPolynomial.eval₂Hom (baseMap.comp MvPolynomial.C) coords

private lemma coneEval_X (j : Fin 5) : coneEval (X j) = coords j := by simp [coneEval]
private lemma coneEval_C (c : K) : coneEval (MvPolynomial.C c) = baseMap (MvPolynomial.C c) := by
  simp [coneEval]

private lemma coneEval_tail (P : Base) : coneEval (tailEmbed P) = baseMap P := by
  have he : coneEval.comp tailEmbed = baseMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [tailEmbed,coneEval]
    · intro j
      fin_cases j <;> simp [tailEmbed,tailIndex,coneEval,coords,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  exact congrArg (fun f : Base →+* ConeRing ↦ f P) he

private lemma coneEval_equation₀ : coneEval equation₀ = 0 := by
  simp only [equation₀,map_sub,map_pow,coneEval_tail,coneEval_X]
  change (QuadraticAlgebra.omega : ConeRing)^2-baseMap radicand₀ = 0
  simp [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk,baseMap,QuadraticAlgebra.algebraMap_eq]

private lemma coneEval_equation₁ : coneEval equation₁ = 0 := by
  simp only [equation₁,map_sub,map_pow,coneEval_tail,coneEval_X]
  change (algebraMap FirstRoot ConeRing QuadraticAlgebra.omega)^2-baseMap radicand₁ = 0
  rw [←map_pow]
  have he : (QuadraticAlgebra.omega : FirstRoot)^2 = algebraMap Base FirstRoot radicand₁ := by
    simp [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk,QuadraticAlgebra.algebraMap_eq]
  rw [he]
  simp [baseMap]

private def quotientMap : Source →+* ConeQuotient := Ideal.Quotient.mk coneIdeal
private def quotientBase : Base →+* ConeQuotient := quotientMap.comp tailEmbed

private lemma quotient_equation₀ : (quotientMap (X 0))^2 = quotientBase radicand₀ := by
  have hmem : equation₀ ∈ coneIdeal := Ideal.subset_span (by simp)
  have hh : quotientMap equation₀ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa [equation₀,quotientBase] using sub_eq_zero.mp hh

private lemma quotient_equation₁ : (quotientMap (X 1))^2 = quotientBase radicand₁ := by
  have hmem : equation₁ ∈ coneIdeal := Ideal.subset_span (by simp)
  have hh : quotientMap equation₁ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa [equation₁,quotientBase] using sub_eq_zero.mp hh

private def firstBack : FirstRoot →+* ConeQuotient :=
  quadraticEval radicand₁ quotientBase (quotientMap (X 1)) quotient_equation₁

private lemma second_root_relation :
    (quotientMap (X 0))^2 = firstBack (algebraMap Base FirstRoot radicand₀) := by
  simpa [firstBack,quadraticEval_apply] using quotient_equation₀

private def coneBack : ConeRing →+* ConeQuotient :=
  quadraticEval (algebraMap Base FirstRoot radicand₀) firstBack
    (quotientMap (X 0)) second_root_relation

private lemma coneBack_base (P : Base) : coneBack (baseMap P) = quotientBase P := by
  simp [coneBack,firstBack,baseMap,quadraticEval_apply]

private lemma coneBack_coneEval (P : Source) : coneBack (coneEval P) = quotientMap P := by
  have he : coneBack.comp coneEval = quotientMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,coneEval_C]
      change coneBack (baseMap (MvPolynomial.C c)) = quotientMap (MvPolynomial.C c)
      rw [coneBack_base]
      simp [quotientBase,tailEmbed]
    · intro j
      simp only [RingHom.comp_apply,coneEval_X]
      change coneBack (coords j) = quotientMap (X j)
      fin_cases j <;> simp [coords,coneBack,firstBack,baseMap,quadraticEval_apply,
        quotientBase,tailEmbed,tailIndex,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
        Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  exact congrArg (fun f : Source →+* ConeQuotient ↦ f P) he

/-- Exact kernel description; no geometric density assertion is assumed. -/
theorem coneEval_eq_zero_iff (P : Source) : coneEval P = 0 ↔ P ∈ coneIdeal := by
  constructor
  · intro h
    have hh := congrArg coneBack h
    rw [coneBack_coneEval,map_zero] at hh
    exact Ideal.Quotient.eq_zero_iff_mem.mp hh
  · intro h
    obtain ⟨a,b,he⟩ := Ideal.mem_span_pair.mp h
    rw [←he,map_add,map_mul,map_mul,coneEval_equation₀,coneEval_equation₁]
    simp

/-- The ideal is fourth-power anisotropic at all polynomial degrees. -/
theorem coneIdeal_fourth_sum (P : Fin 4 → Source)
    (h : (∑ i, P i^4) ∈ coneIdeal) : ∀ i, P i ∈ coneIdeal := by
  have hh := (coneEval_eq_zero_iff _).mpr h
  simp only [map_sum,map_pow] at hh
  have hz := cone_ring_anisotropic (fun i ↦ coneEval (P i)) hh
  exact fun i ↦ (coneEval_eq_zero_iff _).mp (hz i)

end
end Erdos322Research.JointQuadraticCone
