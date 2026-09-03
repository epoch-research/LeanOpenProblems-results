import Submission.ReeBruhatThree
import Submission.DoubleCosetSandwich

/-!
A conditional torus-sandwich transfer of the prime-field Ree certificate.
This does not assert the existence of a torus parameter satisfying trace
constraints, nor identify an abstract finite simple group with these matrices.
-/
noncomputable section
open Matrix SimpleGraph Classical
set_option maxHeartbeats 8000000
namespace Erdos714ReeBruhatSandwich
open Erdos714ReeBruhatThree
variable {F : Type*} [Field F] [Algebra K F]

/-- The conjugates of the *individual* root factors can lie in a smaller
subgroup even though the original prime-field roots do not lie there.
Representatives are `row i * h⁻¹` and `col j * h`, whose inverses are fed to
the right-coset orbital convention. -/
def subgroupCopy (U A : Subgroup (GLF (F := F)))
    (hUA : U ≤ A)
    (hw : matrixMap weyl ∈ A) (hd : matrixMap torus ∈ A)
    (h : GLF (F := F)) (hhA : h ∈ A)
    (hsandwich : h * matrixMap weyl * h = matrixMap weyl)
    (hplus : ∀ t u v : K, h * matrixMap (root t u v) * h⁻¹ ∈ U)
    (hminus : ∀ t u v : K, h⁻¹ * matrixMap (root t u v) * h ∈ U)
    (hplusFix : ∀ x ∈ U, h * x * h⁻¹ ∈
      MulAction.stabilizer (GLF (F := F)) (basePoint (F := F)))
    (hminusFix : ∀ x ∈ U, h⁻¹ * x * h ∈
      MulAction.stabilizer (GLF (F := F)) (basePoint (F := F))) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714DoubleCoset.graph (U.subgroupOf A) (U.subgroupOf A)
        ⟨matrixMap weyl,hw⟩) := by
  have hrootA (t u v : K) : matrixMap (root t u v) ∈ A := by
    have hh := A.mul_mem (A.mul_mem (A.inv_mem hhA) (hUA (hplus t u v))) hhA
    convert hh using 1; group
  let S := MulAction.stabilizer (GLF (F := F)) (basePoint (F := F))
  have hr (i : Fin 4) : matrixMap (row i) ∈ A :=
    row_mem (A.comap matrixMap) hrootA hw hd i
  have hc (i : Fin 4) : matrixMap (col i) ∈ A :=
    col_mem (A.comap matrixMap) hrootA hw i
  let L : Fin 4 → A := fun i => ⟨(matrixMap (row i))⁻¹,A.inv_mem (hr i)⟩
  let R : Fin 4 → A := fun i => ⟨(matrixMap (col i))⁻¹,A.inv_mem (hc i)⟩
  let a : A := ⟨h,hhA⟩
  apply Erdos714DoubleCoset.sandwichCopy (S.subgroupOf A) (S.subgroupOf A)
    (U.subgroupOf A) (U.subgroupOf A) ⟨matrixMap weyl,hw⟩ a a⁻¹ L R
  · intro i j hij
    apply distinguish row row_point_injective S le_rfl i j
    simpa [L] using hij
  · intro i j hij
    apply distinguish col col_point_injective S le_rfl i j
    simpa [R] using hij
  · intro x hx
    exact hminusFix (x : GLF (F := F)) hx
  · intro x hx
    change h * (x : GLF (F := F)) * h⁻¹ ∈ S
    exact hplusFix (x : GLF (F := F)) hx
  · apply Subtype.ext
    exact Erdos714DoubleCoset.inverse_sandwich hsandwich
  · intro i j
    let b := rootTriple (rightFactor i j)
    let c := rootTriple (leftFactor i j)
    let k : A := ⟨(matrixMap b)⁻¹,A.inv_mem (hrootA _ _ _)⟩
    let z : A := ⟨(matrixMap c)⁻¹,A.inv_mem (hrootA _ _ _)⟩
    refine ⟨k,z,?_,?_,?_⟩
    · change h⁻¹ * (matrixMap b)⁻¹ * h ∈ U
      simpa [_root_.mul_inv_rev,mul_assoc] using U.inv_mem (hminus (rightFactor i j).1 (rightFactor i j).2.1 (rightFactor i j).2.2)
    · change h * (matrixMap c)⁻¹ * h⁻¹ ∈ U
      simpa [_root_.mul_inv_rev,mul_assoc] using U.inv_mem
        (hplus (leftFactor i j).1 (leftFactor i j).2.1 (leftFactor i j).2.2)
    · apply Subtype.ext
      have he := congrArg (fun g : G => matrixMap (F := F) g⁻¹) (edge_identity i j)
      simpa [L,R,k,z,c,b,_root_.mul_inv_rev,weyl_inv,mul_assoc] using he

omit [Algebra K F] in
/-- A matrix fixing the distinguished vector also fixes every scalar multiple
of it. Thus a matrix preserving its line conjugates its vector stabilizer to
itself. This statement needs only one eigenvector relation. -/
lemma inverse_conjugate_fixes (h x : GLF (F := F)) (c : F)
    (he : h • (basePoint (F := F)) = c • basePoint)
    (hx : x ∈ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F))) :
    h⁻¹ * x * h ∈ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F)) := by
  have commute_smul (g : GLF (F := F)) (d : F) (v : Fin 7 → F) :
      g • (d • v) = d • (g • v) := Matrix.mulVec_smul _ _ _
  rw [MulAction.mem_stabilizer_iff] at hx ⊢
  rw [SemigroupAction.mul_smul,SemigroupAction.mul_smul,he,commute_smul,hx,← he,inv_smul_smul]

omit [Algebra K F] in
lemma inverse_eigenvector (h : GLF (F := F)) {c : F} (hc : c ≠ 0)
    (he : h • (basePoint (F := F)) = c • basePoint) :
    h⁻¹ • (basePoint (F := F)) = c⁻¹ • basePoint := by
  apply inv_smul_eq_iff.mpr
  have hcomm : h • (c⁻¹ • (basePoint (F := F))) = c⁻¹ • (h • basePoint) :=
    Matrix.mulVec_smul _ _ _
  rw [hcomm,he,smul_smul,inv_mul_cancel₀ hc,one_smul]

/-- For a diagonal torus, distinctness follows from its nonzero first diagonal
entry; no unsupported claim that a quotient biclique lifts to a cover is used. -/
def subgroupCopy_of_eigenvector (U A : Subgroup (GLF (F := F)))
    (hUA : U ≤ A)
    (hw : matrixMap weyl ∈ A) (hd : matrixMap torus ∈ A)
    (h : GLF (F := F)) (hhA : h ∈ A)
    (hsandwich : h * matrixMap weyl * h = matrixMap weyl)
    (hplus : ∀ t u v : K, h * matrixMap (root t u v) * h⁻¹ ∈ U)
    (hminus : ∀ t u v : K, h⁻¹ * matrixMap (root t u v) * h ∈ U)
    (hfix : U ≤ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F)))
    {c : F} (hc : c ≠ 0) (he : h • (basePoint (F := F)) = c • basePoint) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714DoubleCoset.graph (U.subgroupOf A) (U.subgroupOf A)
        ⟨matrixMap weyl,hw⟩) := by
  apply subgroupCopy U A hUA hw hd h hhA hsandwich hplus hminus
  · intro x hx
    simpa only [inv_inv] using
      inverse_conjugate_fixes h⁻¹ x c⁻¹ (inverse_eigenvector h hc he) (hfix hx)
  · intro x hx
    exact inverse_conjugate_fixes h x c he (hfix hx)


end Erdos714ReeBruhatSandwich
#print axioms Erdos714ReeBruhatSandwich.subgroupCopy

#print axioms Erdos714ReeBruhatSandwich.inverse_conjugate_fixes
#print axioms Erdos714ReeBruhatSandwich.inverse_eigenvector
#print axioms Erdos714ReeBruhatSandwich.subgroupCopy_of_eigenvector
