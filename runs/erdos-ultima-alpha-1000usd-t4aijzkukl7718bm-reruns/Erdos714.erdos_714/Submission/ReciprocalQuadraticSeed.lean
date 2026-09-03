import FormalConjecturesUtil

/-!
A kernel-checked K44 in the reciprocal cubic-coordinate quadratic seed over
F5. The chart uses the ACTUAL inverse in F125, in its specified power basis.
This excludes one finite full host, not its thinnings or Erdős 714.
-/
noncomputable section
open Classical Polynomial SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714ReciprocalQuadraticSeed

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev V := Fin 3 → F

def modulus : F[X] := X^3+X+1
lemma modulus_monic : modulus.Monic := by unfold modulus; monicity!
lemma modulus_degree : modulus.natDegree = 3 := by unfold modulus; compute_degree!
lemma modulus_irreducible : Irreducible modulus := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [modulus_degree]; decide
  · have h : ∀ x : F, x^3+x+1 ≠ 0 := by decide
    simpa [modulus,Polynomial.IsRoot.def] using h
instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩
abbrev E := AdjoinRoot modulus

def z : E := AdjoinRoot.root modulus
lemma z_cube : z^3 = -z-1 := by
  have h := AdjoinRoot.eval₂_root modulus
  have hh : z^3+z+1=0 := by simpa [modulus,z] using h
  linear_combination hh
lemma z_fourth : z^4 = -z^2-z := by
  calc
    z^4 = z*z^3 := by ring
    _ = z*(-z-1) := by rw [z_cube]
    _ = -z^2-z := by ring

def pb : PowerBasis F E := AdjoinRoot.powerBasis modulus_monic.ne_zero
lemma pb_dim : pb.dim = 3 := by rw [pb,AdjoinRoot.powerBasis_dim,modulus_degree]
def basis : Module.Basis (Fin 3) F E := pb.basis.reindex (finCongr pb_dim)
lemma basis_pow (i : Fin 3) : basis i = z^(i:ℕ) := by
  rw [basis,Module.Basis.reindex_apply,pb.basis_eq_pow]
  rfl

instance : Fintype E := Fintype.ofEquiv V basis.equivFun.symm.toEquiv
lemma card_E : Fintype.card E = 125 := by
  have h := Fintype.card_congr basis.equivFun.toEquiv
  simpa using h

def element (v : V) : E :=
  algebraMap F E (v 0)+algebraMap F E (v 1)*z+algebraMap F E (v 2)*z^2
lemma element_sum (v : V) : element v = ∑ i : Fin 3, v i • basis i := by
  simp [element,basis_pow,Fin.sum_univ_three,Algebra.smul_def]
lemma element_injective : Function.Injective element := by
  intro v w h
  rw [element_sum,element_sum,← basis.equivFun_symm_apply,← basis.equivFun_symm_apply] at h
  exact basis.equivFun.symm.injective h
lemma coordinates_element (v : V) : basis.equivFun (element v) = v := by
  rw [element_sum,← basis.equivFun_symm_apply,basis.equivFun.apply_symm_apply]

def scalar (t : F) : V := ![t,0,0]
lemma element_scalar (t : F) : element (scalar t) = algebraMap F E t := by
  simp [element,scalar]
lemma element_sub (v w : V) : element (v-w) = element v-element w := by
  simp only [element,Pi.sub_apply,map_sub]
  ring

/-- Polynomial multiplication reduced modulo T^3+T+1. -/
def mul (v w : V) : V :=
  ![v 0*w 0-v 1*w 2-v 2*w 1,
    v 0*w 1+v 1*w 0-v 1*w 2-v 2*w 1-v 2*w 2,
    v 0*w 2+v 1*w 1+v 2*w 0-v 2*w 2]
lemma element_mul (v w : V) : element v*element w = element (mul v w) := by
  simp only [element,mul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,map_add,map_sub,map_mul]
  ring_nf
  rw [z_fourth,z_cube]
  ring
lemma inverse_coordinates (v w : V) (h : mul v w = scalar 1) :
    basis.equivFun ((element v)⁻¹) = w := by
  have hm : element v*element w=1 := by rw [element_mul,h,element_scalar,map_one]
  have hi : (element v)⁻¹=element w := (inv_eq_of_mul_eq_one_right hm)
  rw [hi,coordinates_element]

/-- No replacement inverse or assigned coordinates are used here. -/
def chart (x : E) (t : F) : V := basis.equivFun ((x-algebraMap F E t)⁻¹)
lemma chart_certificate (v w : V) (t : F) (h : mul (v-scalar t) w = scalar 1) :
    chart (element v) t = w := by
  unfold chart
  rw [← element_scalar,← element_sub]
  exact inverse_coordinates _ _ h

def normForm (u v : F) : F := u^2-2*v^2
lemma normForm_anisotropic : ∀ u v : F, normForm u v = 0 → u=0 ∧ v=0 := by decide
lemma quadratic_irreducible : Irreducible (X^2-2 : F[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X^2-2 : F[X]).natDegree = 2 := by compute_degree!
    rw [hd]; decide
  · have h : ∀ x : F, x^2-2 ≠ 0 := by decide
    simpa [Polynomial.IsRoot.def] using h

/-- The quadratic form above is the genuine norm from F25, not an assigned label. -/
instance : Fact (Irreducible (X^2-2 : F[X])) := ⟨quadratic_irreducible⟩
abbrev Q := AdjoinRoot (X^2-2 : F[X])
def theta : Q := AdjoinRoot.root (X^2-2 : F[X])
lemma theta_sq : theta^2 = 2 := by
  have h := AdjoinRoot.eval₂_root (X^2-2 : F[X])
  have hh : theta^2-2=0 := by simpa [theta] using h
  exact sub_eq_zero.mp hh

def qpb : PowerBasis F Q := AdjoinRoot.powerBasis quadratic_irreducible.ne_zero
lemma qpb_dim : qpb.dim = 2 := by
  rw [qpb,AdjoinRoot.powerBasis_dim]
  compute_degree!
def qbasis : Module.Basis (Fin 2) F Q := qpb.basis.reindex (finCongr qpb_dim)
lemma qbasis_pow (i : Fin 2) : qbasis i = theta^(i:ℕ) := by
  rw [qbasis,Module.Basis.reindex_apply,qpb.basis_eq_pow]
  rfl

def quadraticElement (u v : F) : Q := algebraMap F Q u+algebraMap F Q v*theta
lemma leftMul_quadraticElement (u v : F) :
    Algebra.leftMulMatrix qbasis (quadraticElement u v) = !![u,2*v;v,u] := by
  have hc (j : Fin 2) :
      ∑ i : Fin 2, (!![u,2*v;v,u] : Matrix (Fin 2) (Fin 2) F) i j • qbasis i =
        quadraticElement u v*qbasis j := by
    simp only [Fin.sum_univ_two,qbasis_pow,Algebra.smul_def]
    fin_cases j
    · simp [quadraticElement]
    · simp [quadraticElement]
      norm_num only [map_ofNat]
      change 2*(algebraMap F Q v)+(algebraMap F Q u)*theta =
        ((algebraMap F Q u)+(algebraMap F Q v)*theta)*theta
      linear_combination -(algebraMap F Q v)*theta_sq
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,← hc j]
  fin_cases i <;> simp

theorem normForm_eq_norm (u v : F) : normForm u v = Algebra.norm F (quadraticElement u v) := by
  rw [Algebra.norm_eq_matrix_det qbasis,leftMul_quadraticElement,Matrix.det_fin_two]
  simp [normForm]
  ring

/-- The full candidate relation, with both transformed-weight guards. -/
def relation (p q : F × E) : Prop :=
  let v := chart p.2 q.1
  let w := chart q.2 p.1
  v 2 ≠ 0 ∧ w 2 ≠ 0 ∧ normForm (v 0+w 0) (v 1+w 1) = v 2*w 2

def graph : SimpleGraph ((F × E) ⊕ (F × E)) where
  Adj x y := match x,y with
    | .inl p,.inr q => relation p q
    | .inr q,.inl p => relation p q
    | _,_ => False
  symm := by rintro (p|q) (p'|q') <;> exact id
  loopless := by rintro (p|q) h <;> exact h

def rows : Fin 4 → V := ![![0,0,1],![2,3,4],![3,1,2],![3,2,0]]
def cols : Fin 4 → V := ![![0,2,0],![2,3,1],![1,4,1],![2,1,3]]
def tags : Fin 4 → F := ![0,0,1,1]
def rowChart : Fin 4 → Fin 4 → V :=
  ![![![1,4,1],![1,4,1],![2,2,1],![2,2,1]],
    ![![0,4,1],![0,4,1],![0,2,2],![0,2,2]],
    ![![2,4,2],![2,4,2],![4,2,3],![4,2,3]],
    ![![3,4,4],![3,4,4],![1,2,3],![1,2,3]]]
def colChart : Fin 4 → V := ![![2,0,2],![2,2,2],![0,0,1],![0,1,1]]

lemma row_inverses : ∀ i j, mul (rows i-scalar (tags j)) (rowChart i j)=scalar 1 := by decide
lemma col_inverses : ∀ j, mul (cols j-scalar 0) (colChart j)=scalar 1 := by decide
lemma rows_injective : Function.Injective rows := by decide
lemma cols_injective : Function.Injective cols := by decide
lemma edge_values : ∀ i j,
    rowChart i j 2 ≠ 0 ∧ colChart j 2 ≠ 0 ∧
    normForm (rowChart i j 0+colChart j 0) (rowChart i j 1+colChart j 1) =
      rowChart i j 2*colChart j 2 := by decide

lemma actual_row_chart (i j : Fin 4) : chart (element (rows i)) (tags j)=rowChart i j :=
  chart_certificate _ _ _ (row_inverses i j)
lemma actual_col_chart (j : Fin 4) : chart (element (cols j)) 0=colChart j :=
  chart_certificate _ _ _ (col_inverses j)

def left (i : Fin 4) : F × E := (0,element (rows i))
def right (j : Fin 4) : F × E := (tags j,element (cols j))
lemma left_injective : Function.Injective left := by
  intro i j h
  exact rows_injective (element_injective (congrArg Prod.snd h))
lemma right_injective : Function.Injective right := by
  intro i j h
  exact cols_injective (element_injective (congrArg Prod.snd h))
lemma original_edges (i j : Fin 4) : relation (left i) (right j) := by
  dsimp [relation,left,right]
  rw [actual_row_chart,actual_col_chart]
  exact edge_values i j

/-- Four actual rows and columns give the forbidden copy. -/
theorem not_free : ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free graph := by
  intro hf
  apply hf
  refine ⟨⟨⟨Sum.map left right,?_⟩,Sum.map_injective.mpr ⟨left_injective,right_injective⟩⟩⟩
  rintro (i|i) (j|j) h
  · simp at h
  · exact original_edges i j
  · exact original_edges j i
  · simp at h

lemma vertex_count : Fintype.card ((F × E) ⊕ (F × E)) = 1250 := by
  simp [card_E]

#print axioms modulus_irreducible
#print axioms inverse_coordinates
#print axioms quadratic_irreducible
#print axioms normForm_eq_norm
#print axioms original_edges
#print axioms not_free
#print axioms vertex_count
end Erdos714ReciprocalQuadraticSeed
