import Submission.ReeBruhatThree

/-!
The F3 Bruhat certificate persists for the explicitly specified twisted
upper-unitriangular matrix family in any field extension of F3.
This is an obstruction to this family, not to the Erdős conjecture.
-/
noncomputable section
open Matrix SimpleGraph Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
namespace Erdos714ReeBruhatTransfer
open Erdos714ReeBruhatThree

variable {F : Type*} [Field F] [Algebra K F]

/-- The actual seven-dimensional twisted root matrix, with the twisting
endomorphism displayed explicitly rather than encoded as an exponent. -/
def twistedRootMatrix (σ : F →ₐ[K] F) (t u v : F) : Matrix (Fin 7) (Fin 7) F :=
  !![1,σ t,-σ u,σ (t*u)-σ v,-u-(σ t)^3*t-σ (t*v),
     -v-σ (u*v)-(σ t)^3*t^2-σ t*(σ u)^2,
     σ t*v-σ u*u+(σ t)^4*t^2-(σ v)^2-(σ t)^3*t*σ u-σ (t*u*v);
     0,1,t,σ u+σ t*t,-(σ t)^2*t-σ v,
     -(σ u)^2+σ t*t*σ u+t*σ v,
     v+t*u-(σ t)^2*t*σ u-σ (u*v)-(σ t)^3*t^2-σ t*t*σ v;
     0,0,1,σ t,-(σ t)^2,σ v+σ (t*u),u+(σ t)^3*t-σ (t*v)-(σ t)^2*σ u;
     0,0,0,1,σ t,σ u,σ (t*u)-σ v;
     0,0,0,0,1,-t,σ u+σ t*t;
     0,0,0,0,0,1,-σ t;
     0,0,0,0,0,0,1]

lemma twistedRoot_det (σ : F →ₐ[K] F) (t u v : F) :
    (twistedRootMatrix σ t u v).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [twistedRootMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [twistedRootMatrix] at *

def twistedRoot (σ : F →ₐ[K] F) (t u v : F) : GL (Fin 7) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (twistedRootMatrix σ t u v)
    (by rw [twistedRoot_det]; exact one_ne_zero)

/-- Every prime-field root generator is one of the specified twisted roots. -/
lemma mapped_root (σ : F →ₐ[K] F) (t u v : K) :
    matrixMap (root t u v) =
      twistedRoot σ (algebraMap K F t) (algebraMap K F u) (algebraMap K F v) := by
  have h3 (a : K) : (algebraMap K F a)^3 = algebraMap K F a := by
    rw [← map_pow]
    congr 1
    exact ZMod.pow_card a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMap, root, rootMatrix, twistedRoot, twistedRootMatrix,
      Matrix.GeneralLinearGroup.map_apply, map_add, map_sub, map_neg, map_mul, map_pow,
      AlgHom.commutes] <;> ring_nf <;> simp [h3]
  ring

lemma twistedRoot_fixes (σ : F →ₐ[K] F) (t u v : F) :
    twistedRoot σ t u v ∈ MulAction.stabilizer (GL (Fin 7) F) (basePoint (F := F)) := by
  rw [MulAction.mem_stabilizer_iff, smul_basePoint]
  ext i
  fin_cases i <;> simp [twistedRoot,twistedRootMatrix,Matrix.col,basePoint]

/-- The full explicitly generated root subgroup over the extension field. -/
def rootSubgroup (σ : F →ₐ[K] F) : Subgroup (GL (Fin 7) F) :=
  Subgroup.closure {g | ∃ t u v : F, twistedRoot σ t u v = g}

def ambientGroup (σ : F →ₐ[K] F) : Subgroup (GL (Fin 7) F) :=
  rootSubgroup σ ⊔ Subgroup.closure {matrixMap weyl, matrixMap torus}

lemma root_mem (σ : F →ₐ[K] F) (t u v : F) : twistedRoot σ t u v ∈ rootSubgroup σ :=
  Subgroup.subset_closure ⟨t,u,v,rfl⟩

lemma weyl_mem (σ : F →ₐ[K] F) : matrixMap weyl ∈ ambientGroup σ :=
  (show Subgroup.closure {matrixMap weyl,matrixMap torus} ≤ ambientGroup σ from le_sup_right)
    (Subgroup.subset_closure (Set.mem_insert _ _))

lemma torus_mem (σ : F →ₐ[K] F) : matrixMap torus ∈ ambientGroup σ :=
  (show Subgroup.closure {matrixMap weyl,matrixMap torus} ≤ ambientGroup σ from le_sup_right)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The original prime-field copy persists even though the root subgroup
has been enlarged: its first-column distinguishing invariant survives. -/
theorem not_free (σ : F →ₐ[K] F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714DoubleCoset.graph ((rootSubgroup σ).subgroupOf (ambientGroup σ))
        ((rootSubgroup σ).subgroupOf (ambientGroup σ)) ⟨matrixMap weyl,weyl_mem σ⟩) := by
  apply subgroup_not_free (rootSubgroup σ) (ambientGroup σ) le_sup_left
  · intro t u v
    rw [mapped_root σ]
    exact root_mem σ _ _ _
  · exact torus_mem σ
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨t,u,v,rfl⟩
    exact twistedRoot_fixes σ t u v


/-- Enlargement of the ambient group, with the specified full root subgroup,
does not remove this copy. In particular, additional torus generators are
allowed; no assertion of equality with a classified finite group is needed. -/
theorem not_free_in_ambient (σ : F →ₐ[K] F) (A : Subgroup (GL (Fin 7) F))
    (hUA : rootSubgroup σ ≤ A) (hw : matrixMap weyl ∈ A) (hd : matrixMap torus ∈ A) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714DoubleCoset.graph ((rootSubgroup σ).subgroupOf A)
        ((rootSubgroup σ).subgroupOf A) ⟨matrixMap weyl,hw⟩) := by
  apply subgroup_not_free (rootSubgroup σ) A hUA
  · intro t u v
    rw [mapped_root σ]
    exact root_mem σ _ _ _
  · exact hd
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨t,u,v,rfl⟩
    exact twistedRoot_fixes σ t u v

/-- The exponent twist used in the Ree representation. -/
def frobeniusTwist (m : ℕ) : F →ₐ[K] F := FiniteField.frobeniusAlgHom K F ^ m

lemma frobeniusTwist_apply (m : ℕ) (x : F) : frobeniusTwist m x = x^(3^m) := by
  induction m with
  | zero => simp [frobeniusTwist]
  | succ m ih =>
    rw [frobeniusTwist, pow_succ, AlgHom.mul_apply]
    change (FiniteField.frobeniusAlgHom K F ^ m) (x^3) = _
    rw [map_pow]
    change (frobeniusTwist m x)^3 = _
    rw [ih, ← pow_mul, Nat.pow_succ]

/-- In particular the obstruction persists for each iterated Frobenius twist.
No finite-field cardinality assumption or unproved root-generator inclusion
is required for this explicitly matrix-generated graph. -/
theorem frobenius_not_free (m : ℕ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714DoubleCoset.graph
        ((rootSubgroup (frobeniusTwist (F := F) m)).subgroupOf (ambientGroup (frobeniusTwist m)))
        ((rootSubgroup (frobeniusTwist m)).subgroupOf (ambientGroup (frobeniusTwist m)))
        ⟨matrixMap weyl,weyl_mem (frobeniusTwist m)⟩) :=
  not_free (frobeniusTwist m)

#print axioms not_free_in_ambient
#print axioms frobeniusTwist_apply
#print axioms frobenius_not_free
#print axioms mapped_root
#print axioms twistedRoot_fixes
#print axioms not_free
end Erdos714ReeBruhatTransfer
