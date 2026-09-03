import Submission.DoubleCosetOrbital

/-!
A concrete root-subgroup double-coset obstruction in the seven-dimensional
Ree matrices over F3. This does not settle Erdős Problem 714.
-/
noncomputable section
open Matrix SimpleGraph Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
namespace Erdos714ReeBruhatThree
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev K := ZMod 3
abbrev M := Matrix (Fin 7) (Fin 7) K
abbrev G := GL (Fin 7) K

def rootMatrix (t u v : K) : M :=
  !![1,t,-u,t*u-v,-u-t^4-t*v,-v-u*v-t^5-t*u^2,t*v-u^2+t^6-v^2-t^4*u-t*u*v;
     0,1,t,u+t^2,-t^3-v,-u^2+t^2*u+t*v,v+t*u-t^3*u-u*v-t^5-t^2*v;
     0,0,1,t,-t^2,v+t*u,u+t^4-t*v-t^2*u;
     0,0,0,1,t,u,t*u-v;
     0,0,0,0,1,-t,u+t^2;
     0,0,0,0,0,1,-t;
     0,0,0,0,0,0,1]

def formMatrix : M := !![0,0,0,0,0,0,1;0,0,0,0,0,1,0;0,0,0,0,1,0,0;
  0,0,0,-1,0,0,0;0,0,1,0,0,0,0;0,1,0,0,0,0,0;1,0,0,0,0,0,0]
def orthogonalInverse (A : M) : M := formMatrix*A.transpose*formMatrix

lemma root_inverse : ∀ t u v : K,
    rootMatrix t u v * orthogonalInverse (rootMatrix t u v) = 1 ∧
    orthogonalInverse (rootMatrix t u v) * rootMatrix t u v = 1 := by decide

def root (t u v : K) : G :=
  ⟨rootMatrix t u v,orthogonalInverse (rootMatrix t u v),(root_inverse t u v).1,(root_inverse t u v).2⟩

def weylMatrix : M := !![0,0,0,0,0,0,-1;0,0,0,0,0,-1,0;0,0,0,0,-1,0,0;
  0,0,0,-1,0,0,0;0,0,-1,0,0,0,0;0,-1,0,0,0,0,0;-1,0,0,0,0,0,0]
def torusMatrix : M := diagonal ![-1,1,-1,1,-1,1,-1]
lemma weyl_square : weylMatrix*weylMatrix = 1 := by decide
lemma torus_square : torusMatrix*torusMatrix = 1 := by decide
def weyl : G := ⟨weylMatrix,weylMatrix,weyl_square,weyl_square⟩
def torus : G := ⟨torusMatrix,torusMatrix,torus_square,torus_square⟩
lemma weyl_inv : weyl⁻¹ = weyl := by rfl

def row : Fin 4 → G := ![1,weyl,root 0 0 1*torus*weyl,root 0 0 2*torus*weyl]
def col : Fin 4 → G := ![root 0 1 0*weyl,root 0 2 0*weyl,root 1 0 2*weyl,root 1 1 0*weyl]
def rootTriple (x : K × K × K) : G := root x.1 x.2.1 x.2.2

def leftFactor : Fin 4 → Fin 4 → K × K × K :=
  ![![(0,1,0),(0,2,0),(1,0,2),(1,1,0)],
    ![(0,2,0),(0,1,0),(2,0,1),(2,1,0)],
    ![(0,1,1),(1,1,2),(2,2,0),(0,2,2)],
    ![(0,1,2),(2,1,1),(2,0,0),(1,2,2)]]
def rightFactor : Fin 4 → Fin 4 → K × K × K :=
  ![![(0,0,0),(0,0,0),(0,0,0),(0,0,0)],
    ![(0,2,0),(0,1,0),(0,0,1),(2,1,0)],
    ![(2,1,1),(0,2,2),(1,2,0),(0,1,1)],
    ![(1,1,2),(0,2,1),(2,1,2),(2,0,0)]]

/-- All sixteen original double-coset identities, not just invariant values. -/
lemma edge_identity : ∀ i j : Fin 4,
    (row i)⁻¹*col j = rootTriple (leftFactor i j)*weyl*rootTriple (rightFactor i j) := by decide

lemma row_point_injective : Function.Injective (fun i => (row i : M).col 0) := by decide
lemma col_point_injective : Function.Injective (fun i => (col i : M).col 0) := by decide
lemma root_column : ∀ t u v : K, (root t u v : M).col 0 = Pi.single 0 1 := by decide


lemma row_mem (S : Subgroup G) (hroot : ∀ t u v : K, root t u v ∈ S)
    (hw : weyl ∈ S) (hd : torus ∈ S) (i : Fin 4) : row i ∈ S := by
  fin_cases i
  · exact S.one_mem
  · exact hw
  · exact S.mul_mem (S.mul_mem (hroot 0 0 1) hd) hw
  · exact S.mul_mem (S.mul_mem (hroot 0 0 2) hd) hw

lemma col_mem (S : Subgroup G) (hroot : ∀ t u v : K, root t u v ∈ S)
    (hw : weyl ∈ S) (i : Fin 4) : col i ∈ S := by
  fin_cases i
  · exact S.mul_mem (hroot 0 1 0) hw
  · exact S.mul_mem (hroot 0 2 0) hw
  · exact S.mul_mem (hroot 1 0 2) hw
  · exact S.mul_mem (hroot 1 1 0) hw

section Transfer
variable {F : Type*} [Field F] [Algebra K F]
abbrev GLF := GL (Fin 7) F
abbrev matrixMap : G →* GLF (F := F) := Matrix.GeneralLinearGroup.map (algebraMap K F)
def basePoint : Fin 7 → F := Pi.single 0 1

omit [Algebra K F] in
lemma smul_basePoint (g : GLF (F := F)) :
    g • basePoint = (g : Matrix (Fin 7) (Fin 7) F).col 0 := by
  change (g : Matrix (Fin 7) (Fin 7) F).mulVec (Pi.single 0 1) = _
  simp [Matrix.mulVec_single]

lemma mapped_root_fixes (t u v : K) :
    matrixMap (F := F) (root t u v) ∈ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F)) := by
  rw [MulAction.mem_stabilizer_iff,smul_basePoint]
  ext i
  change algebraMap K F ((root t u v : M) i 0) = (Pi.single (0 : Fin 7) (1 : F) : Fin 7 → F) i
  have h := congrFun (root_column t u v) i
  change (root t u v : M) i 0 = (Pi.single (0 : Fin 7) (1 : K) : Fin 7 → K) i at h
  rw [h]
  simp [Pi.single_apply]

/-- The first column distinguishes cosets even if the root subgroup is enlarged. -/
lemma distinguish {r : ℕ} (a : Fin r → G)
    (ha : Function.Injective (fun i => (a i : M).col 0))
    (U : Subgroup (GLF (F := F))) (hfix : U ≤ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F)))
    (i j : Fin r) (h : (matrixMap (a j))⁻¹*matrixMap (a i) ∈ U) : i = j := by
  have hp := (MulAction.mem_stabilizer_iff.mp (hfix h))
  have he : matrixMap (F := F) (a i) • (basePoint (F := F)) = matrixMap (F := F) (a j) • (basePoint (F := F)) := by
    have he := congrArg
      (fun v : Fin 7 → F => matrixMap (F := F) (a j) • v) hp
    simpa only [← SemigroupAction.mul_smul, mul_inv_cancel_left] using he
  rw [smul_basePoint,smul_basePoint] at he
  apply ha
  ext k
  apply (algebraMap K F).injective
  exact congrFun he k

/-- The actual quotient-graph copy lies inside ANY ambient matrix subgroup
containing these root matrices and the Weyl and torus elements. -/
def subgroupCopy (U A : Subgroup (GLF (F := F)))
    (hUA : U ≤ A)
    (hroot : ∀ t u v : K, matrixMap (root t u v) ∈ U)
    (hw : matrixMap weyl ∈ A) (hd : matrixMap torus ∈ A)
    (hfix : U ≤ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F))) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714DoubleCoset.graph (U.subgroupOf A) (U.subgroupOf A) ⟨matrixMap weyl,hw⟩) := by
  have hr (i : Fin 4) : matrixMap (row i) ∈ A :=
    row_mem (A.comap matrixMap) (fun t u v => hUA (hroot t u v)) hw hd i
  have hc (i : Fin 4) : matrixMap (col i) ∈ A :=
    col_mem (A.comap matrixMap) (fun t u v => hUA (hroot t u v)) hw i
  let L : Fin 4 → A := fun i => ⟨(matrixMap (row i))⁻¹,A.inv_mem (hr i)⟩
  let R : Fin 4 → A := fun i => ⟨(matrixMap (col i))⁻¹,A.inv_mem (hc i)⟩
  apply Erdos714DoubleCoset.representativesCopy (U.subgroupOf A) (U.subgroupOf A)
    ⟨matrixMap weyl,hw⟩ L R
  · intro i j hij
    apply distinguish row row_point_injective U hfix i j
    simpa [L] using hij
  · intro i j hij
    apply distinguish col col_point_injective U hfix i j
    simpa [R] using hij
  · intro i j
    let b := rootTriple (rightFactor i j)
    let a := rootTriple (leftFactor i j)
    have hb : matrixMap b ∈ U := hroot _ _ _
    have ha : matrixMap a ∈ U := hroot _ _ _
    let k : A := ⟨(matrixMap b)⁻¹,A.inv_mem (hUA hb)⟩
    let h : A := ⟨(matrixMap a)⁻¹,A.inv_mem (hUA ha)⟩
    refine ⟨k,U.inv_mem hb,h,U.inv_mem ha,?_⟩
    apply Subtype.ext
    have he := congrArg (fun g : G => matrixMap (F := F) g⁻¹) (edge_identity i j)
    simpa [L,R,k,h,a,b,_root_.mul_inv_rev,weyl_inv,mul_assoc] using he

theorem subgroup_not_free (U A : Subgroup (GLF (F := F)))
    (hUA : U ≤ A) (hroot : ∀ t u v : K, matrixMap (root t u v) ∈ U)
    (hw : matrixMap weyl ∈ A) (hd : matrixMap torus ∈ A)
    (hfix : U ≤ MulAction.stabilizer (GLF (F := F)) (basePoint (F := F))) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714DoubleCoset.graph (U.subgroupOf A) (U.subgroupOf A) ⟨matrixMap weyl,hw⟩) :=
  fun hf => hf ⟨subgroupCopy U A hUA hroot hw hd hfix⟩

end Transfer

/-- The explicitly generated F3 root subgroup. -/
def rootSubgroup : Subgroup G := Subgroup.closure {g | ∃ t u v : K, root t u v = g}
/-- The explicitly generated seven-dimensional matrix group. -/
def ambientGroup : Subgroup G := rootSubgroup ⊔ Subgroup.closure {weyl,torus}

lemma root_mem (t u v : K) : root t u v ∈ rootSubgroup :=
  Subgroup.subset_closure ⟨t,u,v,rfl⟩
lemma weyl_mem : weyl ∈ ambientGroup :=
  (show Subgroup.closure {weyl,torus} ≤ ambientGroup from le_sup_right)
    (Subgroup.subset_closure (Set.mem_insert _ _))
lemma torus_mem : torus ∈ ambientGroup :=
  (show Subgroup.closure {weyl,torus} ≤ ambientGroup from le_sup_right)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- No unsupplied group-classification, invariant, or irreducibility assumption remains. -/
theorem not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714DoubleCoset.graph (rootSubgroup.subgroupOf ambientGroup)
        (rootSubgroup.subgroupOf ambientGroup) ⟨weyl,weyl_mem⟩) := by
  have hmap : matrixMap (F := K) = MonoidHom.id G := by
    ext g i j
    rfl
  have hf : rootSubgroup ≤ MulAction.stabilizer G (basePoint (F := K)) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨t,u,v,rfl⟩
    simpa only [hmap,MonoidHom.id_apply] using mapped_root_fixes (F := K) t u v
  have hh := subgroup_not_free (F := K) rootSubgroup ambientGroup le_sup_left
    (fun t u v => by simpa only [hmap,MonoidHom.id_apply] using root_mem t u v)
    (by simpa only [hmap,MonoidHom.id_apply] using weyl_mem)
    (by simpa only [hmap,MonoidHom.id_apply] using torus_mem) hf
  simpa only [hmap,MonoidHom.id_apply] using hh

#print axioms mapped_root_fixes
#print axioms distinguish
#print axioms subgroupCopy
#print axioms subgroup_not_free
#print axioms not_free

#print axioms root_inverse
#print axioms edge_identity
#print axioms row_point_injective
#print axioms col_point_injective
end Erdos714ReeBruhatThree
