import FormalConjecturesUtil

/-!
A checked failure of the projected quadratic graph candidate at q=11.
The connection condition is x=z^2 and t=Algebra.trace(z), with t nonzero.
The certificate uses the actual cubic field and actual algebra trace; even
all point coordinates and vertex weights are nonzero. This is not a
disproof of Erdős 714.
-/

noncomputable section
open Classical Polynomial SimpleGraph
set_option maxHeartbeats 3000000

namespace Erdos714SquareTraceProjection

abbrev K := ZMod 11
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def modulus : K[X] := X^3-X^2+X-3
lemma modulus_monic : modulus.Monic := by unfold modulus; monicity!
lemma modulus_degree : modulus.natDegree = 3 := by unfold modulus; compute_degree!
lemma modulus_irreducible : Irreducible modulus := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [modulus_degree]; decide
  · have h : ∀ x : K, x^3-x^2+x-3 ≠ 0 := by decide
    simpa [modulus,Polynomial.IsRoot.def] using h
instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩

abbrev E := AdjoinRoot modulus
instance : CharP E 11 := charP_of_injective_algebraMap (algebraMap K E).injective 11

def z : E := AdjoinRoot.root modulus
lemma z_cube : z^3 = z^2-z+3 := by
  have h := AdjoinRoot.eval₂_root modulus
  have hh : z^3-z^2+z-3=0 := by simpa [modulus,z] using h
  linear_combination hh
lemma z_fourth : z^4=2*z+3 := by
  calc
    z^4=z*z^3 := by ring
    _=z*(z^2-z+3) := by rw [z_cube]
    _=z^3-z^2+3*z := by ring
    _=2*z+3 := by rw [z_cube]; ring

def pb : PowerBasis K E := AdjoinRoot.powerBasis modulus_monic.ne_zero
lemma pb_dim : pb.dim=3 := by rw [pb,AdjoinRoot.powerBasis_dim,modulus_degree]
def basis : Module.Basis (Fin 3) K E := pb.basis.reindex (finCongr pb_dim)
lemma basis_pow (i : Fin 3) : basis i=z^(i:ℕ) := by
  rw [basis, Module.Basis.reindex_apply, pb.basis_eq_pow]
  rfl

abbrev V := Fin 3 → K

def element (v : V) : E :=
  algebraMap K E (v 0)+algebraMap K E (v 1)*z+algebraMap K E (v 2)*z^2

lemma element_add (v w : V) : element (v+w)=element v+element w := by
  simp only [element,Pi.add_apply,map_add]
  ring
lemma element_zero : element 0=0 := by simp [element]
lemma element_sum (v : V) : element v=∑ i : Fin 3, v i • basis i := by
  simp [element,basis_pow,Fin.sum_univ_three,Algebra.smul_def]
lemma element_injective : Function.Injective element := by
  intro v w h
  rw [element_sum,element_sum,← basis.equivFun_symm_apply,← basis.equivFun_symm_apply] at h
  exact basis.equivFun.symm.injective h
lemma element_ne_zero {v : V} (h : v ≠ 0) : element v ≠ 0 := by
  intro he
  exact h (element_injective (he.trans element_zero.symm))

/-- Squaring reduced using z^3=z^2-z+3 and z^4=2*z+3. -/
def square (v : V) : V :=
  ![v 0^2+6*v 1*v 2+3*v 2^2,
    2*v 0*v 1-2*v 1*v 2+2*v 2^2,
    v 1^2+2*v 0*v 2+2*v 1*v 2]

lemma element_square (v : V) : element v^2=element (square v) := by
  simp only [element,square,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_sub,map_mul,map_pow,map_ofNat]
  ring_nf
  rw [z_fourth,z_cube]
  ring

def companion : Matrix (Fin 3) (Fin 3) K := !![0,0,3;1,0,-1;0,1,1]
lemma leftMul_z : Algebra.leftMulMatrix basis z=companion := by
  have hcol (j : Fin 3) : ∑ i : Fin 3, companion i j • basis i=z*basis j := by
    simp only [Fin.sum_univ_three,basis_pow,Algebra.smul_def]
    fin_cases j
    · simp [companion]
    · simp [companion,pow_two]
    · simp [companion, map_ofNat]
      linear_combination -z_cube
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,← hcol j]
  simp [Finsupp.single_apply]

lemma trace_z : Algebra.trace K E z=1 := by
  rw [Algebra.trace_eq_matrix_trace basis,leftMul_z]
  decide
lemma trace_z_sq : Algebra.trace K E (z^2) = -1 := by
  rw [Algebra.trace_eq_matrix_trace basis,map_pow,leftMul_z]
  decide
lemma finrank_E : Module.finrank K E=3 := by
  simpa using Module.finrank_eq_card_basis basis

/-- The coordinate trace is proved equal to the actual algebra trace. -/
def traceForm (v : V) : K := 3*v 0+v 1-v 2
lemma trace_element (v : V) : Algebra.trace K E (element v)=traceForm v := by
  have hm (a : K) (x : E) :
      Algebra.trace K E (algebraMap K E a*x)=a*Algebra.trace K E x :=
    by simpa only [Algebra.smul_def, smul_eq_mul] using (Algebra.trace K E).map_smul a x
  simp only [element,map_add,hm,Algebra.trace_algebraMap,finrank_E,trace_z,trace_z_sq,
    traceForm,nsmul_eq_mul]
  ring

/-- A translated certificate, so no zero point coordinate or zero weight is used. -/
def rows : Fin 4 → V := ![![0,1,0],![10,1,0],![2,1,0],![1,1,0]]
def cols : Fin 4 → V := ![![0,10,1],![0,3,5],![10,6,5],![0,10,1]]
def weights : Fin 4 → K := ![10,10,10,8]
def roots : Fin 4 → Fin 4 → V :=
  ![![![0,1,0],![8,5,6],![4,5,5],![0,10,0]],
    ![![10,1,8],![7,4,2],![6,6,1],![1,10,3]],
    ![![9,3,7],![0,10,9],![3,9,6],![2,8,4]],
    ![![8,6,7],![1,3,5],![3,2,10],![3,5,4]]]

lemma rows_injective : Function.Injective rows := by decide
lemma cols_weights_injective : Function.Injective (fun j => (cols j,weights j)) := by decide
lemma rows_ne_zero : ∀ i, rows i ≠ 0 := by decide
lemma cols_ne_zero : ∀ j, cols j ≠ 0 := by decide
lemma weights_ne_zero : ∀ j, weights j ≠ 0 := by decide
lemma sums_ne_zero : ∀ j, (2:K)+weights j ≠ 0 := by decide
lemma square_certificate : ∀ i j, square (roots i j)=rows i+cols j := by decide
lemma trace_certificate : ∀ i j, traceForm (roots i j)=(2:K)+weights j := by decide

/-- The ORIGINAL projected-square incidence relation, including all nonzero filters. -/
def relation (p q : E × K) : Prop :=
  p.1≠0 ∧ q.1≠0 ∧ p.2≠0 ∧ q.2≠0 ∧ p.2+q.2≠0 ∧
    ∃ u : E, u^2=p.1+q.1 ∧ Algebra.trace K E u=p.2+q.2

def graph : SimpleGraph ((E × K) ⊕ (E × K)) where
  Adj v w := match v,w with
    | .inl p,.inr q => relation p q
    | .inr q,.inl p => relation p q
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

lemma certificate_edge (i j : Fin 4) :
    relation (element (rows i),2) (element (cols j),weights j) := by
  refine ⟨element_ne_zero (rows_ne_zero i),element_ne_zero (cols_ne_zero j),(by decide : (2 : K) ≠ 0),
    weights_ne_zero j,sums_ne_zero j,element (roots i j),?_,?_⟩
  · rw [element_square,square_certificate,element_add]
  · rw [trace_element,trace_certificate]

/-- A genuine K44 copy in the actual field/trace graph, not merely coordinate formulas. -/
def copy : (completeBipartiteGraph (Fin 4) (Fin 4)).Copy graph where
  toHom := {
    toFun := Sum.elim (fun i => Sum.inl (element (rows i),(2:K)))
      (fun j => Sum.inr (element (cols j),weights j))
    map_rel' := by
      intro v w h
      cases v with
      | inl i =>
        cases w with
        | inl j => simp at h
        | inr j => exact certificate_edge i j
      | inr i =>
        cases w with
        | inl j => exact certificate_edge j i
        | inr j => simp at h }
  injective' := by
    intro v w h
    cases v with
    | inl i =>
      cases w with
      | inl j =>
        exact congrArg Sum.inl (rows_injective (element_injective
          (congrArg Prod.fst (Sum.inl.inj h))))
      | inr j => cases h
    | inr i =>
      cases w with
      | inl j => cases h
      | inr j =>
        apply congrArg Sum.inr
        apply cols_weights_injective
        have he := Sum.inr.inj h
        apply Prod.ext
        · exact element_injective (congrArg Prod.fst he)
        · exact congrArg (fun p : E × K => p.2) he

theorem not_free : ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free graph := fun h => h ⟨copy⟩

end Erdos714SquareTraceProjection

#print axioms Erdos714SquareTraceProjection.modulus_irreducible
#print axioms Erdos714SquareTraceProjection.trace_element
#print axioms Erdos714SquareTraceProjection.certificate_edge
#print axioms Erdos714SquareTraceProjection.copy
#print axioms Erdos714SquareTraceProjection.not_free
