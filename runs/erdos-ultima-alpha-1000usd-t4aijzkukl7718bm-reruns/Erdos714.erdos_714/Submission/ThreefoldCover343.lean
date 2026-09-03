import FormalConjecturesUtil

/-! A concrete obstruction to the threefold multiplicative norm cover at
q=343. This is not a disproof of the conjecture in Spec.lean. -/
noncomputable section
open Classical Polynomial SimpleGraph
set_option maxHeartbeats 8000000
namespace Erdos714ThreefoldCover343
abbrev F := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev V := Fin 9 → F

def modulus : F[X] := X^9-C 2
lemma modulus_monic : modulus.Monic := monic_X_pow_sub_C _ (by decide)
lemma modulus_degree : modulus.natDegree=9 := natDegree_X_pow_sub_C
lemma modulus_irreducible : Irreducible modulus := by
  have h : ∀ x : F, x^3 ≠ 2 := by decide
  exact X_pow_sub_C_irreducible_of_prime_pow (by decide : Nat.Prime 3) (by decide) 2 h
instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩
abbrev E := AdjoinRoot modulus
instance : CharP E 7 := charP_of_injective_algebraMap (algebraMap F E).injective 7
def z : E := AdjoinRoot.root modulus
lemma z_ninth : z^9=2 := by
  have h := AdjoinRoot.eval₂_root modulus
  have hh : z^9-2=0 := by simpa [modulus,z] using h
  exact sub_eq_zero.mp hh

def pb : PowerBasis F E := AdjoinRoot.powerBasis modulus_monic.ne_zero
lemma pb_dim : pb.dim=9 := by rw [pb,AdjoinRoot.powerBasis_dim,modulus_degree]
def basis : Module.Basis (Fin 9) F E := pb.basis.reindex (finCongr pb_dim)
lemma basis_pow (i : Fin 9) : basis i=z^(i:ℕ) := by
  rw [basis,Module.Basis.reindex_apply,pb.basis_eq_pow]
  rfl
instance : Fintype E := Fintype.ofEquiv V basis.equivFun.symm.toEquiv
lemma card_E : Fintype.card E=343^3 := by
  have h := Fintype.card_congr basis.equivFun.toEquiv
  simpa using h

def element (v : V) : E := ∑ i : Fin 9, algebraMap F E (v i)*z^(i:ℕ)
lemma element_sum (v : V) : element v=∑ i : Fin 9, v i • basis i := by
  simp [element,basis_pow,Algebra.smul_def]
lemma element_injective : Function.Injective element := by
  intro v w h
  rw [element_sum,element_sum,←basis.equivFun_symm_apply,←basis.equivFun_symm_apply] at h
  exact basis.equivFun.symm.injective h
lemma element_zero : element (0 : V)=0 := by simp [element]
lemma element_add (v w : V) : element (v+w)=element v+element w := by
  simp [element,map_add,add_mul,Finset.sum_add_distrib]
lemma z_reduce (n : ℕ) : z^n=(2:E)^(n/9)*z^(n%9) := by
  rw [←z_ninth,←pow_mul,←pow_add]
  congr 1
  omega

def mul (v w : V) : V :=
  ![v 0*w 0+2*v 1*w 8+2*v 2*w 7+2*v 3*w 6+2*v 4*w 5+2*v 5*w 4+2*v 6*w 3+2*v 7*w 2+2*v 8*w 1,
    v 0*w 1+v 1*w 0+2*v 2*w 8+2*v 3*w 7+2*v 4*w 6+2*v 5*w 5+2*v 6*w 4+2*v 7*w 3+2*v 8*w 2,
    v 0*w 2+v 1*w 1+v 2*w 0+2*v 3*w 8+2*v 4*w 7+2*v 5*w 6+2*v 6*w 5+2*v 7*w 4+2*v 8*w 3,
    v 0*w 3+v 1*w 2+v 2*w 1+v 3*w 0+2*v 4*w 8+2*v 5*w 7+2*v 6*w 6+2*v 7*w 5+2*v 8*w 4,
    v 0*w 4+v 1*w 3+v 2*w 2+v 3*w 1+v 4*w 0+2*v 5*w 8+2*v 6*w 7+2*v 7*w 6+2*v 8*w 5,
    v 0*w 5+v 1*w 4+v 2*w 3+v 3*w 2+v 4*w 1+v 5*w 0+2*v 6*w 8+2*v 7*w 7+2*v 8*w 6,
    v 0*w 6+v 1*w 5+v 2*w 4+v 3*w 3+v 4*w 2+v 5*w 1+v 6*w 0+2*v 7*w 8+2*v 8*w 7,
    v 0*w 7+v 1*w 6+v 2*w 5+v 3*w 4+v 4*w 3+v 5*w 2+v 6*w 1+v 7*w 0+2*v 8*w 8,
    v 0*w 8+v 1*w 7+v 2*w 6+v 3*w 5+v 4*w 4+v 5*w 3+v 6*w 2+v 7*w 1+v 8*w 0]
lemma element_mul (v w : V) : element (mul v w)=element v*element w := by
  simp only [element,mul,Fin.sum_univ_succ]
  dsimp
  simp only [map_add,map_mul,map_ofNat]
  ring_nf
  rw [z_reduce 9, z_reduce 10, z_reduce 11, z_reduce 12, z_reduce 13, z_reduce 14, z_reduce 15, z_reduce 16]
  norm_num
  ring

def frob (v : V) : V := ![v 0,v 4,v 8,4*v 3,4*v 7,2*v 2,2*v 6,v 1,v 5]
lemma element_frob (v : V) : element (frob v)=(element v)^7 := by
  have h (a : F) : (AdjoinRoot.of modulus a)^7=AdjoinRoot.of modulus a := by
    rw [←map_pow]
    congr 1
    exact ZMod.pow_card a
  simp only [element,Fin.sum_univ_succ,Fin.sum_univ_zero]
  dsimp [frob]
  simp only [map_mul,map_ofNat]
  simp only [add_pow_char,mul_pow,h,←pow_mul]
  rw [z_reduce 14, z_reduce 21, z_reduce 28, z_reduce 35, z_reduce 42, z_reduce 49, z_reduce 56]
  norm_num
  have h7 : (7 : E)=0 := CharP.cast_eq_zero E 7
  linear_combination -(AdjoinRoot.of modulus (v 4)*z +
    9*AdjoinRoot.of modulus (v 8)*z^2 +
    4*AdjoinRoot.of modulus (v 7)*z^4 +
    2*AdjoinRoot.of modulus (v 6)*z^6 +
    AdjoinRoot.of modulus (v 5)*z^8)*h7

/-- Explicit addition/Frobenius chains; every multiplication is checked below. -/
def inputs : Fin 18 → V :=
  ![![0,5,0,0,6,2,1,2,3],
    ![1,6,5,6,1,2,4,2,6],
    ![3,6,1,5,4,5,3,5,4],
    ![4,1,2,6,0,6,2,5,2],
    ![1,5,0,0,6,2,1,2,3],
    ![2,6,5,6,1,2,4,2,6],
    ![4,6,1,5,4,5,3,5,4],
    ![5,1,2,6,0,6,2,5,2],
    ![2,5,0,0,6,2,1,2,3],
    ![3,6,5,6,1,2,4,2,6],
    ![5,6,1,5,4,5,3,5,4],
    ![6,1,2,6,0,6,2,5,2],
    ![0,6,0,0,6,2,1,2,3],
    ![1,0,5,6,1,2,4,2,6],
    ![3,0,1,5,4,5,3,5,4],
    ![4,2,2,6,0,6,2,5,2],
    ![0,4,4,3,0,2,2,4,3],
    ![4,3,2,2,5,0,1,1,2]]

def table : Fin 18 → Fin 9 → V :=
  ![![![0,5,0,0,6,2,1,2,3],
    ![3,4,4,6,4,3,2,0,0],
    ![0,4,1,6,4,0,6,4,5],
    ![1,5,4,5,5,1,2,4,2],
    ![0,1,5,2,5,3,3,3,0],
    ![1,4,0,0,1,2,1,6,1],
    ![3,6,1,4,5,0,6,0,3],
    ![4,2,3,6,3,5,5,2,3],
    ![0,4,0,0,3,0,0,1,0]],
    ![![1,6,5,6,1,2,4,2,6],
    ![2,1,6,4,4,5,0,2,3],
    ![4,4,0,4,1,0,0,6,2],
    ![4,4,6,4,4,1,0,1,2],
    ![0,0,2,3,0,2,0,2,3],
    ![2,4,0,2,6,2,1,5,0],
    ![1,3,5,5,1,2,3,6,0],
    ![1,4,2,3,6,1,5,5,1],
    ![0,6,0,0,4,0,0,4,0]],
    ![![3,6,1,5,4,5,3,5,4],
    ![6,5,3,0,1,4,2,1,2],
    ![6,5,6,6,5,6,1,1,5],
    ![2,4,4,0,3,0,3,4,1],
    ![4,0,4,0,1,4,0,2,5],
    ![4,5,4,0,5,2,5,3,2],
    ![5,3,1,6,2,3,4,3,1],
    ![6,1,0,5,5,4,3,4,3],
    ![3,0,0,3,0,0,4,0,0]],
    ![![4,1,2,6,0,6,2,5,2],
    ![0,6,1,5,6,5,6,6,1],
    ![1,3,5,4,1,3,2,4,2],
    ![5,1,6,4,3,1,2,2,1],
    ![6,1,0,5,1,4,6,1,1],
    ![2,5,6,2,1,1,5,1,6],
    ![4,1,6,6,1,4,6,4,1],
    ![5,4,3,4,0,3,6,5,0],
    ![0,0,0,0,3,0,0,2,0]],
    ![![1,5,0,0,6,2,1,2,3],
    ![4,0,4,6,2,0,4,4,6],
    ![1,0,5,2,5,1,5,2,0],
    ![1,5,6,2,2,3,4,2,3],
    ![2,5,2,0,2,5,2,4,0],
    ![3,0,3,2,4,1,6,5,0],
    ![0,0,1,6,2,2,4,3,0],
    ![1,0,1,2,3,5,0,3,1],
    ![0,4,0,0,3,0,0,1,0]],
    ![![2,6,5,6,1,2,4,2,6],
    ![5,6,2,2,6,2,1,6,1],
    ![6,1,6,6,1,1,2,1,4],
    ![2,6,1,0,5,0,6,2,0],
    ![6,5,3,6,5,0,3,6,1],
    ![4,4,3,6,0,2,5,0,3],
    ![2,5,2,4,1,4,5,5,4],
    ![6,1,5,1,3,0,1,2,5],
    ![0,6,0,0,4,0,0,4,0]],
    ![![4,6,1,5,4,5,3,5,4],
    ![6,3,5,3,2,0,1,4,3],
    ![3,5,4,1,6,2,5,0,4],
    ![6,2,2,3,2,3,0,1,4],
    ![3,6,6,2,2,0,6,4,5],
    ![0,0,2,4,1,5,2,0,0],
    ![1,2,3,5,0,3,1,2,4],
    ![0,4,1,6,2,1,0,4,5],
    ![3,0,0,3,0,0,4,0,0]],
    ![![5,1,2,6,0,6,2,5,2],
    ![2,1,5,3,6,3,3,2,5],
    ![4,1,4,2,6,3,1,4,3],
    ![3,4,3,6,1,3,1,2,2],
    ![5,6,3,4,0,3,6,4,6],
    ![2,2,4,3,4,2,1,4,4],
    ![0,0,1,6,3,5,2,0,3],
    ![0,0,4,6,4,1,0,2,1],
    ![0,0,0,0,3,0,0,2,0]],
    ![![2,5,0,0,6,2,1,2,3],
    ![0,3,4,6,0,4,6,1,5],
    ![3,3,1,0,2,2,3,6,4],
    ![2,5,1,5,4,4,6,6,3],
    ![4,5,5,1,5,4,5,5,0],
    ![1,5,2,4,2,5,5,5,2],
    ![2,4,3,0,6,5,5,4,1],
    ![3,6,6,4,6,2,1,1,4],
    ![0,5,0,0,3,0,0,4,0]],
    ![![3,6,5,6,1,2,4,2,6],
    ![3,4,5,0,1,6,2,3,6],
    ![0,0,1,4,3,5,2,5,4],
    ![5,1,1,6,1,2,5,5,6],
    ![1,1,2,1,0,4,4,1,1],
    ![4,6,5,0,0,4,1,4,1],
    ![6,2,5,0,2,4,3,5,3],
    ![1,5,0,4,0,6,2,3,6],
    ![0,6,0,0,1,0,0,3,0]],
    ![![5,6,1,5,4,5,3,5,4],
    ![1,1,0,6,3,3,0,0,4],
    ![4,6,6,4,3,5,0,5,4],
    ![0,2,4,0,5,6,3,0,3],
    ![3,6,3,2,0,1,5,4,3],
    ![5,6,0,3,3,3,2,6,1],
    ![0,5,5,5,5,3,3,3,1],
    ![3,6,1,2,0,6,5,1,6],
    ![6,0,0,4,0,0,4,0,0]],
    ![![6,1,2,6,0,6,2,5,2],
    ![6,3,2,1,6,1,0,5,2],
    ![5,4,0,1,6,4,1,0,1],
    ![3,3,6,0,1,0,2,5,5],
    ![4,1,2,4,0,5,5,1,3],
    ![3,5,4,3,4,6,0,5,0],
    ![1,6,2,5,6,0,3,0,5],
    ![5,6,0,6,0,0,0,4,2],
    ![0,3,0,0,0,0,0,4,0]],
    ![![0,6,0,0,6,2,1,2,3],
    ![1,4,1,6,4,1,6,2,4],
    ![2,2,2,3,2,3,5,1,1],
    ![5,0,6,6,4,1,4,1,1],
    ![4,4,1,2,5,6,3,5,0],
    ![2,6,0,4,2,5,6,2,0],
    ![3,0,0,3,4,4,0,2,2],
    ![6,5,5,0,2,5,0,1,0],
    ![0,0,0,0,0,2,0,0,4]],
    ![![1,0,5,6,1,2,4,2,6],
    ![5,3,5,0,2,0,4,3,0],
    ![1,6,6,6,2,2,4,5,6],
    ![3,2,2,5,5,3,2,3,3],
    ![4,6,6,1,2,3,3,0,2],
    ![1,2,2,0,2,4,6,3,0],
    ![4,2,1,0,2,5,5,0,5],
    ![3,1,4,5,0,0,0,4,3],
    ![0,0,0,0,0,0,0,0,1]],
    ![![3,0,1,5,4,5,3,5,4],
    ![1,4,2,2,4,5,5,0,5],
    ![5,3,6,3,2,3,0,0,3],
    ![0,2,3,2,3,6,3,1,2],
    ![4,4,1,1,2,5,1,4,0],
    ![3,5,1,3,1,4,1,5,0],
    ![0,0,2,3,6,4,2,4,5],
    ![0,1,2,6,2,2,3,0,5],
    ![0,0,0,0,6,0,0,0,0]],
    ![![4,2,2,6,0,6,2,5,2],
    ![1,0,4,2,4,5,4,3,4],
    ![0,6,0,6,5,3,1,3,6],
    ![2,4,0,0,6,1,3,2,4],
    ![1,0,0,1,6,5,2,6,5],
    ![3,5,0,0,1,1,3,2,4],
    ![0,6,5,1,3,1,1,6,4],
    ![5,6,6,2,3,0,2,0,3],
    ![0,0,3,0,0,5,0,0,4]],
    ![![0,4,4,3,0,2,2,4,3],
    ![3,6,5,2,5,3,3,1,4],
    ![6,6,0,0,6,1,5,5,5],
    ![2,3,3,0,6,0,3,3,1],
    ![6,6,3,2,6,4,2,3,0],
    ![6,2,3,1,4,1,6,3,5],
    ![1,6,0,6,5,1,6,5,1],
    ![1,0,5,4,4,5,4,6,4],
    ![0,0,0,6,0,0,0,0,0]],
    ![![4,3,2,2,5,0,1,1,2],
    ![0,5,5,0,4,6,5,0,2],
    ![3,3,5,6,3,3,2,6,3],
    ![0,3,3,5,5,0,2,6,6],
    ![3,2,0,0,4,4,4,2,1],
    ![4,0,0,4,1,6,0,5,2],
    ![3,2,3,1,4,2,5,5,1],
    ![5,1,1,1,6,0,5,1,2],
    ![0,3,0,0,4,0,0,6,0]]]

lemma table_zero (k : Fin 18) : table k 0=inputs k := by fin_cases k <;> decide
lemma step1 (k : Fin 18) : mul (table k 0) (table k 0)=table k 1 := by
  fin_cases k <;> decide
lemma step2 (k : Fin 18) : mul (table k 1) (table k 1)=table k 2 := by
  fin_cases k <;> decide
lemma step3 (k : Fin 18) : mul (table k 2) (table k 0)=table k 3 := by
  fin_cases k <;> decide
lemma step4 (k : Fin 18) : mul (frob (table k 1)) (table k 1)=table k 4 := by
  fin_cases k <;> decide
lemma step5 (k : Fin 18) : mul (frob (table k 4)) (table k 1)=table k 5 := by
  fin_cases k <;> decide
lemma step6 (k : Fin 18) : mul (frob (table k 5)) (table k 2)=table k 6 := by
  fin_cases k <;> decide
lemma step7 (k : Fin 18) : mul (frob (table k 6)) (table k 2)=table k 7 := by
  fin_cases k <;> decide
lemma step8 (k : Fin 18) : mul (frob (table k 7)) (table k 3)=table k 8 := by
  fin_cases k <;> decide

lemma power_values (k : Fin 18) : element (inputs k)^39331=element (table k 8) := by
  have h0 : element (table k 0)=element (inputs k)^1 := by rw [table_zero,pow_one]
  have h1 : element (table k 1)=element (inputs k)^2 := by
    rw [←step1,element_mul,h0,←pow_add]
  have h2 : element (table k 2)=element (inputs k)^4 := by
    rw [←step2,element_mul,h1,←pow_add]
  have h3 : element (table k 3)=element (inputs k)^5 := by
    rw [←step3,element_mul,h2,h0,←pow_add]
  have h4 : element (table k 4)=element (inputs k)^16 := by
    rw [←step4,element_mul,element_frob,h1,←pow_mul,←pow_add]
  have h5 : element (table k 5)=element (inputs k)^114 := by
    rw [←step5,element_mul,element_frob,h4,h1,←pow_mul,←pow_add]
  have h6 : element (table k 6)=element (inputs k)^802 := by
    rw [←step6,element_mul,element_frob,h5,h2,←pow_mul,←pow_add]
  have h7 : element (table k 7)=element (inputs k)^5618 := by
    rw [←step7,element_mul,element_frob,h6,h2,←pow_mul,←pow_add]
  symm
  rw [←step8,element_mul,element_frob,h7,h3,←pow_mul,←pow_add]

def pointRows : Fin 4 → V :=
  ![![0,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0],
    ![2,0,0,0,0,0,0,0,0],
    ![0,1,0,0,0,0,0,0,0]]
def pointColumns : Fin 4 → V :=
  ![![0,5,0,0,6,2,1,2,3],
    ![1,6,5,6,1,2,4,2,6],
    ![3,6,1,5,4,5,3,5,4],
    ![4,1,2,6,0,6,2,5,2]]
def rowWeights : Fin 4 → V :=
  ![![1,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0],
    ![0,0,0,6,0,0,0,0,0],
    ![0,3,0,0,4,0,0,6,0]]
def columnWeights : Fin 4 → V :=
  ![![0,4,0,0,3,0,0,1,0],
    ![0,6,0,0,4,0,0,4,0],
    ![3,0,0,3,0,0,4,0,0],
    ![0,0,0,0,3,0,0,2,0]]
def rowPreimages : Fin 4 → V :=
  ![![1,0,0,0,0,0,0,0,0],
    ![1,0,0,0,0,0,0,0,0],
    ![0,4,4,3,0,2,2,4,3],
    ![4,3,2,2,5,0,1,1,2]]

def edgeIndex (i j : Fin 4) : Fin 18 := ⟨4*i.val+j.val,by omega⟩
lemma input_edges (i j : Fin 4) : pointRows i+pointColumns j=inputs (edgeIndex i j) := by
  fin_cases i <;> fin_cases j <;> decide
lemma output_edges (i j : Fin 4) :
    table (edgeIndex i j) 8=mul (rowWeights i) (columnWeights j) := by
  fin_cases i <;> fin_cases j <;> decide
lemma edge_equations (i j : Fin 4) :
    (element (pointRows i)+element (pointColumns j))^39331=
      element (rowWeights i)*element (columnWeights j) := by
  rw [←element_add,input_edges,power_values,output_edges,element_mul]

lemma row_preimages (i : Fin 4) :
    (element (rowPreimages i))^39331=element (rowWeights i) := by
  fin_cases i
  · norm_num [rowPreimages,rowWeights,element,Fin.sum_univ_succ]
  · norm_num [rowPreimages,rowWeights,element,Fin.sum_univ_succ]
  · exact power_values 16
  · exact power_values 17
lemma column_preimages (j : Fin 4) :
    element (pointColumns j)^39331=element (columnWeights j) := by
  have h := edge_equations 0 j
  simpa [pointRows,rowWeights,element,Fin.sum_univ_succ] using h

lemma row_preimages_ne_zero (i : Fin 4) : element (rowPreimages i) ≠ 0 := by
  intro h
  have he : rowPreimages i=0 := element_injective (h.trans element_zero.symm)
  have hn : rowPreimages i ≠ 0 := by fin_cases i <;> decide
  exact hn he
lemma column_points_ne_zero (j : Fin 4) : element (pointColumns j) ≠ 0 := by
  intro h
  have he : pointColumns j=0 := element_injective (h.trans element_zero.symm)
  have hn : pointColumns j ≠ 0 := by fin_cases j <;> decide
  exact hn he

/-- The labels are precisely actual nonzero power images. -/
def Weight := {a : E // ∃ u : E, u ≠ 0 ∧ u^39331=a}
lemma weight_ne_zero (a : Weight) : a.val ≠ 0 := by
  obtain ⟨u,hu,hp⟩ := a.property
  rw [←hp]
  exact pow_ne_zero _ hu

/-- Identification with the actual image subgroup, rather than an assigned
label count. -/
def weightEquiv : Weight ≃ (powMonoidHom 39331 : Eˣ →* Eˣ).range where
  toFun a := ⟨Units.mk0 a.val (weight_ne_zero a),by
    obtain ⟨u,hu,hp⟩ := a.property
    refine ⟨Units.mk0 u hu,?_⟩
    apply Units.ext
    exact hp⟩
  invFun a := ⟨a.val.val,by
    obtain ⟨u,hu⟩ := a.property
    exact ⟨u.val,u.ne_zero,congrArg Units.val hu⟩⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext (Units.ext rfl)

instance : Fintype Weight := Fintype.ofEquiv (powMonoidHom 39331 : Eˣ →* Eˣ).range weightEquiv.symm
lemma card_weights : Fintype.card Weight=3*(343-1) := by
  rw [Fintype.card_congr weightEquiv,←Nat.card_eq_fintype_card,
    IsCyclic.card_powMonoidHom_range]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_units,card_E]
lemma vertex_count : Fintype.card ((E × Weight) ⊕ (E × Weight))=
    2*343^3*(3*(343-1)) := by
  simp only [Fintype.card_sum,Fintype.card_prod,card_E,card_weights]
  norm_num

def rowLabel (i : Fin 4) : Weight :=
  ⟨element (rowWeights i),element (rowPreimages i),row_preimages_ne_zero i,row_preimages i⟩
def columnLabel (j : Fin 4) : Weight :=
  ⟨element (columnWeights j),element (pointColumns j),column_points_ne_zero j,column_preimages j⟩
def graph : SimpleGraph ((E × Weight) ⊕ (E × Weight)) where
  Adj p q := match p,q with
    | .inl p,.inr q => (p.1+q.1)^39331=p.2.val*q.2.val
    | .inr p,.inl q => (q.1+p.1)^39331=q.2.val*p.2.val
    | _,_ => False
  symm := by intro p q h; cases p <;> cases q <;> exact h
  loopless := by intro p; cases p <;> simp

lemma rows_injective : Function.Injective pointRows := by decide
lemma columns_injective : Function.Injective pointColumns := by decide

def rows : Fin 4 ↪ E × Weight :=
  ⟨fun i => (element (pointRows i),rowLabel i),by
    intro i j h
    exact rows_injective (element_injective (congrArg Prod.fst h))⟩
def columns : Fin 4 ↪ E × Weight :=
  ⟨fun j => (element (pointColumns j),columnLabel j),by
    intro i j h
    exact columns_injective (element_injective (congrArg Prod.fst h))⟩

def copy : (completeBipartiteGraph (Fin 4) (Fin 4)).Copy graph := by
  refine ⟨⟨rows.sumMap columns,?_⟩,(rows.sumMap columns).injective⟩
  intro p q hpq
  cases p with
  | inl i => cases q with
    | inl j => simp at hpq
    | inr j => exact edge_equations i j
  | inr j => cases q with
    | inr i => simp at hpq
    | inl i => exact edge_equations i j

theorem not_free : ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free graph :=
  fun h => h ⟨copy⟩

#print axioms modulus_irreducible
#print axioms card_E
#print axioms element_mul
#print axioms element_frob
#print axioms power_values
#print axioms edge_equations
#print axioms card_weights
#print axioms vertex_count
#print axioms not_free
end Erdos714ThreefoldCover343
