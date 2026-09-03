import Submission.QuaternionCubicNorm

/-!
A constant-norm cyclic-four orbit survives an arbitrary field-endomorphism
on the central coordinate of a Kummer cubic norm model. This identification
need not be linear over the norm's base field. This is a construction
obstruction, not a proof or disproof of Erdős 714.
-/
noncomputable section
open Polynomial SimpleGraph Classical
set_option maxHeartbeats 4000000
namespace Erdos714SemilinearCenterNorm
open Erdos714QuaternionCubicNorm (Root center cocycle square center_square cyclicCopy weightedGraph)
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The two-coordinate part of a cubic Kummer norm, identified with the actual
multiplication matrix, not an assumed coordinate norm. -/
lemma norm_plane (d : F) (a : E) (ha : a^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=a^(i:ℕ)) (y z : F) :
    Algebra.norm F (algebraMap F E y*a+algebraMap F E z*a^2)=d*y^3+d^2*z^3 := by
  let M : Matrix (Fin 3) (Fin 3) F := !![0,d*z,d*y;y,0,d*z;z,y,0]
  have ha4 : a^4=algebraMap F E d*a := by
    calc
      a^4=a^3*a := by ring
      _ = _ := by rw [ha]
  have hcol (j : Fin 3) : ∑ i, M i j • B i=
      (algebraMap F E y*a+algebraMap F E z*a^2)*B j := by
    simp only [Fin.sum_univ_three,hB,Algebra.smul_def]
    fin_cases j
    · change algebraMap F E 0 * a^0 + algebraMap F E y * a^1 +
        algebraMap F E z * a^2 = _
      simp only [map_zero]
      ring
    · change algebraMap F E (d*z) * a^0 + algebraMap F E 0 * a^1 +
        algebraMap F E y * a^2 = _
      simp only [map_mul,map_zero]
      ring_nf
      rw [ha]
      ring
    · change algebraMap F E (d*y) * a^0 + algebraMap F E (d*z) * a^1 +
        algebraMap F E 0 * a^2 = _
      simp only [map_mul,map_zero]
      ring_nf
      rw [ha4,ha]
      ring
  have hm : Algebra.leftMulMatrix B (algebraMap F E y*a+algebraMap F E z*a^2)=M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul,← hcol j]
    simp [Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det B,hm]
  simp [M,Matrix.det_fin_three]
  ring

/-- A genuine Kummer power basis makes the orbit weight nonzero automatically. -/
lemma common_weight_ne_zero (d : F) (a : E) (ha : a^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=a^(i:ℕ)) : d+d^2 ≠ 0 := by
  have hvec : B 1+B 2 ≠ 0 := by
    intro h
    have hcoord := congrArg (fun x => B.repr x (1 : Fin 3)) h
    simp at hcoord
  have hnorm := (Algebra.norm_ne_zero_iff_of_basis B).mpr hvec
  have hval : B 1+B 2=algebraMap F E 1*a+algebraMap F E 1*a^2 := by
    simp [hB]
  rw [hval,norm_plane d a ha B hB] at hnorm
  simpa only [one_pow,mul_one] using hnorm

/-- Only the central coordinate is twisted. -/
def value (eta : F) (σ : F →+* F) (a : E) (g : Root F eta) : E :=
  algebraMap F E g.x+algebraMap F E g.y*a+algebraMap F E (σ g.z)*a^2

def graph (eta : F) (σ : F →+* F) (a : E) :
    SimpleGraph ((Root F eta × Fˣ) ⊕ (Root F eta × Fˣ)) :=
  weightedGraph (fun g => Algebra.norm F (value eta σ a g))

section CharacteristicTwo
variable [CharP F 2]

lemma cube_root_identities (eta : F) (he : eta^2+eta+1=0) :
    eta^2=eta+1 ∧ eta^3=1 ∧ (eta+1)^3=1 := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  have he2 : eta^2=eta+1 := by linear_combination he-(eta+1)*h2
  have he3 : eta^3=1 := by
    linear_combination (eta-1)*he
  refine ⟨he2,he3,?_⟩
  linear_combination he3+he+(eta^2+eta)*h2

def generator (eta : F) : Root F eta := ⟨0,eta,eta⟩
def initial (eta : F) : Root F eta := ⟨0,eta+1,eta⟩
def orbit (eta : F) : Fin 4 → Root F eta :=
  ![⟨0,eta+1,eta⟩,⟨0,1,eta⟩,⟨0,eta+1,eta+1⟩,⟨0,1,eta+1⟩]

lemma generator_square (eta : F) (he : eta^2+eta+1=0) :
    (generator eta)^2=center eta 1 := by
  rw [square]
  congr 1
  change Erdos714QuaternionNormPlane.quad eta 0 eta=1
  simpa [Erdos714QuaternionNormPlane.quad,pow_succ,mul_assoc] using
    (cube_root_identities eta he).2.1

lemma generator_fourth (eta : F) (he : eta^2+eta+1=0) :
    (generator eta)^4=1 := by
  rw [show (4:ℕ)=2*2 by rfl,pow_mul,generator_square eta he,center_square]

lemma generator_square_ne_one (eta : F) (he : eta^2+eta+1=0) :
    (generator eta)^2 ≠ 1 := by
  rw [generator_square eta he]
  exact Erdos714QuaternionCubicNorm.center_ne_one eta one_ne_zero

lemma orbit_formula (eta : F) (he : eta^2+eta+1=0) (i : Fin 4) :
    (generator eta)^(i:ℕ)*initial eta=orbit eta i := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  have hmul : generator eta*initial eta=(⟨0,1,eta⟩ : Root F eta) := by
    apply Root.ext
    · change 0+0=0; ring
    · change eta+(eta+1)=1
      linear_combination eta*h2
    · change eta+eta+(0*0+0*(eta+1)+eta*eta*(eta+1))=eta
      linear_combination eta*he
  fin_cases i
  · change (generator eta)^0*initial eta=initial eta
    rw [pow_zero,one_mul]
  · change (generator eta)^1*initial eta=⟨0,1,eta⟩
    rw [pow_one,hmul]
  · change (generator eta)^2*initial eta=⟨0,eta+1,eta+1⟩
    rw [generator_square eta he]
    apply Root.ext
    · change 0+0=0; ring
    · change 0+(eta+1)=eta+1; ring
    · change 1+eta+(0*0+0*(eta+1)+eta*0*(eta+1))=eta+1
      ring
  · change (generator eta)^3*initial eta=⟨0,1,eta+1⟩
    rw [show (3:ℕ)=2+1 by rfl,pow_succ,generator_square eta he,mul_assoc,hmul]
    apply Root.ext
    · change 0+0=0; ring
    · change 0+1=1; ring
    · change 1+eta+(0*0+0*1+eta*0*1)=eta+1
      ring

/-- Every endomorphism preserves the relevant cubes; it need not fix eta. -/
lemma orbit_norm (eta d : F) (he : eta^2+eta+1=0)
    (σ : F →+* F) (a : E) (ha : a^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=a^(i:ℕ)) (i : Fin 4) :
    Algebra.norm F (value eta σ a (orbit eta i))=d+d^2 := by
  have h3 := (cube_root_identities eta he).2.1
  have h4 := (cube_root_identities eta he).2.2
  have hσ3 : (σ eta)^3=1 := by rw [← map_pow,h3,map_one]
  have hσ4 : (σ (eta+1))^3=1 := by rw [← map_pow,h4,map_one]
  have hnorm (y z : F) (hy : y^3=1) (hz : (σ z)^3=1) :
      Algebra.norm F (value eta σ a (⟨0,y,z⟩ : Root F eta))=d+d^2 := by
    change Algebra.norm F (algebraMap F E 0 + algebraMap F E y*a +
      algebraMap F E (σ z)*a^2)=_
    rw [map_zero,zero_add,norm_plane d a ha B hB,hy,hz,mul_one,mul_one]
  fin_cases i
  · exact hnorm (eta+1) eta h4 hσ3
  · exact hnorm 1 eta (one_pow _) hσ3
  · exact hnorm (eta+1) (eta+1) h4 hσ4
  · exact hnorm 1 (eta+1) (one_pow _) hσ4

/-- A genuine K44 using the original inverse-relative group law. -/
def copy (eta d : F) (he : eta^2+eta+1=0) (hd : d+d^2 ≠ 0)
    (σ : F →+* F) (a : E) (ha : a^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=a^(i:ℕ)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph eta σ a) := by
  apply cyclicCopy (fun g => Algebra.norm F (value eta σ a g))
    (generator eta) (initial eta) (d+d^2) hd
    (generator_fourth eta he) (generator_square_ne_one eta he)
  intro i
  rw [orbit_formula eta he]
  exact orbit_norm eta d he σ a ha B hB i

theorem not_free (eta d : F) (he : eta^2+eta+1=0) (hd : d+d^2 ≠ 0)
    (σ : F →+* F) (a : E) (ha : a^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=a^(i:ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph eta σ a) :=
  fun hf => hf ⟨copy eta d he hd σ a ha B hB⟩

/-- No separate condition on the common weight is needed for an actual basis. -/
theorem not_free_kummer (eta d : F) (he : eta^2+eta+1=0)
    (σ : F →+* F) (a : E) (ha : a^3=algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i=a^(i:ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph eta σ a) :=
  not_free eta d he (common_weight_ne_zero d a ha B hB) σ a ha B hB

end CharacteristicTwo
end Erdos714SemilinearCenterNorm
#print axioms Erdos714SemilinearCenterNorm.norm_plane
#print axioms Erdos714SemilinearCenterNorm.cube_root_identities
#print axioms Erdos714SemilinearCenterNorm.generator_fourth
#print axioms Erdos714SemilinearCenterNorm.orbit_formula
#print axioms Erdos714SemilinearCenterNorm.orbit_norm
#print axioms Erdos714SemilinearCenterNorm.not_free

#print axioms Erdos714SemilinearCenterNorm.common_weight_ne_zero
#print axioms Erdos714SemilinearCenterNorm.not_free_kummer
