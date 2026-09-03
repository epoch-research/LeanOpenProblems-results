import Submission.QuinticNormProduct
import Submission.CubicTraceNormPlane

/-!
An actual square-weight cubic norm graph obstruction in characteristic seven.
The certificate was obtained by translating and inverting an opposite-weight
grid. The proof below checks the final coordinates and all sixteen norms;
it does not trust the computation used to find the inversion pole.
This does not prove or disprove Erdős 714.
-/
noncomputable section
open Polynomial SimpleGraph Classical
set_option maxHeartbeats 4000000
namespace Erdos714OddSquareNormSeven
open Erdos714QuinticNormProduct (element multiplicationMatrix leftMulMatrix_element)
abbrev K := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev V := Fin 3 → K

def rows : Fin 4 → V := ![![5,2,5],![2,3,1],![2,0,4],![5,2,3]]
def cols : Fin 4 → V := ![![6,5,1],![5,6,1],![6,2,6],![4,5,5]]
def rowWeight : Fin 4 → K := ![1,2,1,2]
def colWeight : Fin 4 → K := ![4,2,1,4]
def rowRoot : Fin 4 → K := ![1,3,1,3]
def colRoot : Fin 4 → K := ![2,3,1,2]
def coordinateNorm (v : V) : K := (multiplicationMatrix 2 (v 0) (v 1) (v 2)).det

lemma row_injective : Function.Injective rows := by decide
lemma col_injective : Function.Injective cols := by decide
lemma row_nonzero : ∀ i, rowWeight i ≠ 0 := by decide
lemma col_nonzero : ∀ i, colWeight i ≠ 0 := by decide
lemma row_square : ∀ i, rowWeight i = rowRoot i * rowRoot i := by decide
lemma col_square : ∀ i, colWeight i = colRoot i * colRoot i := by decide
lemma coordinate_edges : ∀ i j, coordinateNorm (rows i + cols j) = rowWeight i * colWeight j := by
  decide

lemma polynomial_irreducible : Irreducible (X^3-X-2 : K[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : (X^3-X-2 : K[X]).natDegree = 3 := by compute_degree!
    rw [h]; decide
  · have h : ∀ x : K, x^3-x-2 ≠ 0 := by decide
    simpa [Polynomial.IsRoot] using h

section ActualNorm
variable {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E]

/-- Actual nonzero square weights, not duplicated labels for square roots. -/
def Weight (F : Type*) [Field F] := {a : F // a ≠ 0 ∧ IsSquare a}

def graph : SimpleGraph ((E × Weight F) ⊕ (E × Weight F)) where
  Adj v w := match v,w with
    | .inl p,.inr q => Algebra.norm F (p.1+q.1) = p.2.val*q.2.val
    | .inr q,.inl p => Algebra.norm F (p.1+q.1) = p.2.val*q.2.val
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

omit [Algebra K F] in
/-- The exact translated-inversion identity used to obtain the certificate.
Neither translated point may be the inversion pole. -/
lemma inversion_norm [FiniteDimensional F E] (x y z : E)
    (hx : x+z ≠ 0) (hy : y-z ≠ 0) :
    Algebra.norm F ((x+z)⁻¹+(y-z)⁻¹) =
      Algebra.norm F (x+y)/(Algebra.norm F (x+z)*Algebra.norm F (y-z)) := by
  apply (eq_div_iff (mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hx)
    (Algebra.norm_ne_zero_iff.mpr hy))).mpr
  rw [← map_mul,← map_mul]
  congr 1
  field_simp
  ring

/-- Interpret the prime-field certificate in a cubic power basis over F. -/
def point (z : E) (v : V) : E := element z
  (algebraMap K F (v 0)) (algebraMap K F (v 1)) (algebraMap K F (v 2))

lemma point_add (z : E) (v w : V) : point (F := F) z (v+w) = point (F := F) z v+point (F := F) z w := by
  simp only [point,element,Pi.add_apply,map_add]
  ring

lemma point_injective (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i = z^(i : ℕ)) : Function.Injective (point (F := F) z) := by
  have he (v : V) : point (F := F) z v = ∑ i : Fin 3, algebraMap K F (v i) • B i := by
    simp [point,element,Fin.sum_univ_three,hB,Algebra.smul_def]
  intro v w hvw
  rw [he,he,← B.equivFun_symm_apply,← B.equivFun_symm_apply] at hvw
  have hh := B.equivFun.symm.injective hvw
  funext i
  exact (algebraMap K F).injective (congrFun hh i)

lemma norm_point (z : E) (hz : z^3=z+algebraMap F E (2:F))
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z^(i : ℕ)) (v : V) :
    Algebra.norm F (point (F := F) z v) = algebraMap K F (coordinateNorm v) := by
  rw [point,Algebra.norm_eq_matrix_det B,leftMulMatrix_element 2 z hz B hB]
  have h2 : algebraMap K F (2:K) = (2:F) := map_ofNat (algebraMap K F) 2
  simp [coordinateNorm,multiplicationMatrix,Matrix.det_fin_three]
  rw [h2]

/-- All sixteen edges in the actual norm graph, in every supplied cubic basis. -/
lemma norm_edges (z : E) (hz : z^3=z+algebraMap F E (2:F))
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z^(i : ℕ)) (i j : Fin 4) :
    Algebra.norm F (point (F := F) z (rows i)+point (F := F) z (cols j)) =
      algebraMap K F (rowWeight i)*algebraMap K F (colWeight j) := by
  rw [← point_add,norm_point (F := F) z hz B hB,coordinate_edges,map_mul]

def rowWeight' (i : Fin 4) : Weight F :=
  ⟨algebraMap K F (rowWeight i),
    (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr (row_nonzero i),
    ⟨algebraMap K F (rowRoot i),by rw [row_square,map_mul]⟩⟩

def colWeight' (i : Fin 4) : Weight F :=
  ⟨algebraMap K F (colWeight i),
    (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr (col_nonzero i),
    ⟨algebraMap K F (colRoot i),by rw [col_square,map_mul]⟩⟩

def powerBasisCopy (z : E) (hz : z^3=z+algebraMap F E (2:F))
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z^(i : ℕ)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph (F := F) (E := E)) := by
  let L : Fin 4 ↪ E × Weight F := ⟨fun i => (point (F := F) z (rows i),rowWeight' i),by
    intro i j hij
    exact row_injective (point_injective z B hB (congrArg Prod.fst hij))⟩
  let R : Fin 4 ↪ E × Weight F := ⟨fun i => (point (F := F) z (cols i),colWeight' i),by
    intro i j hij
    exact col_injective (point_injective z B hB (congrArg Prod.fst hij))⟩
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro v w hvw
  cases v with
  | inl i =>
    cases w with
    | inl j => simp at hvw
    | inr j => exact norm_edges z hz B hB i j
  | inr j =>
    cases w with
    | inl i => exact norm_edges z hz B hB i j
    | inr i => simp at hvw

/-- Irreducibility is explicit: it cannot be dropped in arbitrary base extensions. -/
theorem not_free_of_irreducible [Fintype F] [Fintype E]
    (hp : Irreducible (X^3-X-2 : F[X])) (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  have hp' : Irreducible (Erdos714CubicTraceNormPlane.pencil (0:F) (-1) 2) := by
    simpa [Erdos714CubicTraceNormPlane.pencil] using hp
  obtain ⟨pb,hpb,hmin⟩ := Erdos714CubicTraceNormPlane.exists_powerBasis hdim 0 (-1) 2 hp'
  let B := pb.basis.reindex (finCongr hpb)
  have hB (i : Fin 3) : B i=pb.gen^(i:ℕ) := by simp [B]
  have hz : pb.gen^3=pb.gen+algebraMap F E (2:F) := by
    have hh := minpoly.aeval F pb.gen
    rw [hmin] at hh
    simp [Erdos714CubicTraceNormPlane.pencil] at hh
    linear_combination hh
  exact fun hf => hf ⟨powerBasisCopy pb.gen hz B hB⟩

end ActualNorm

/-- In particular this excludes every model of the cubic extension of F7. -/
theorem seven_not_free {E : Type*} [Field E] [Algebra K E] [Fintype E]
    (hdim : Module.finrank K E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := K) (E := E)) :=
  not_free_of_irreducible polynomial_irreducible hdim


/-- The prime-field irreducible cubic cannot acquire a root in an extension
whose degree is not divisible by three. -/
theorem irreducible_of_base_degree {F : Type*} [Field F] [Algebra K F]
    (hm : ¬ 3 ∣ Module.finrank K F) : Irreducible (X^3-X-2 : F[X]) := by
  have hdeg : (X^3-X-2 : K[X]).natDegree = 3 := by compute_degree!
  have hmon : (X^3-X-2 : K[X]).Monic := by monicity; norm_num
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : (X^3-X-2 : F[X]).natDegree = 3 := by compute_degree!
    rw [h]; decide
  · intro x hx
    have he : Polynomial.aeval x (X^3-X-2 : K[X]) = 0 := by
      have h2 : Polynomial.aeval x (2:K[X]) = (2:F) := map_ofNat (Polynomial.aeval x) 2
      simp only [map_sub,map_pow,Polynomial.aeval_X,h2]
      simpa [Polynomial.IsRoot] using hx
    have hi : IsIntegral K x := ⟨_,hmon,he⟩
    have hmin := minpoly.eq_of_irreducible_of_monic polynomial_irreducible he hmon
    have hd := minpoly.degree_dvd hi
    rw [← hmin,hdeg] at hd
    exact hm hd

/-- Uniformly over all base extensions of F7 of degree not divisible by three,
with the actual norm of any finite cubic extension of that base. -/
theorem not_free_of_base_degree {F E : Type*} [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Fintype F] [Fintype E]
    (hm : ¬ 3 ∣ Module.finrank K F) (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) :=
  not_free_of_irreducible (irreducible_of_base_degree hm) hdim

/-- This includes the unbounded field orders 7^(6k+1), where minus one is
nonsquare. The argument is not an extrapolation from one finite test. -/
theorem not_free_of_card {F E : Type*} [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Fintype F] [Fintype E]
    (m : ℕ) (hcard : Fintype.card F = 7^m) (hm : ¬ 3 ∣ m)
    (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  have he : Module.finrank K F = m :=
    Nat.pow_right_injective (by decide : 2 ≤ 7)
      ((FiniteField.pow_finrank_eq_card 7 F).trans hcard)
  exact not_free_of_base_degree (he ▸ hm) hdim


/-- A nonfree square-weight family with nonsquare minus one at every base
order 7^(6k+1). This excludes this sequence, not all possible field sequences. -/
theorem nonsquare_family {F E : Type*} [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Fintype F] [Fintype E]
    (k : ℕ) (hcard : Fintype.card F = 7^(6*k+1)) (hdim : Module.finrank F E = 3) :
    ¬ IsSquare (-1:F) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  constructor
  · rw [FiniteField.isSquare_neg_one_iff,hcard]
    have h : 7^(6*k+1) % 4 = 3 := by
      rw [pow_add,pow_mul]
      norm_num [Nat.mul_mod,Nat.pow_mod]
    exact fun hn => hn h
  · exact not_free_of_card (6*k+1) hcard (by omega) hdim

end Erdos714OddSquareNormSeven
#print axioms Erdos714OddSquareNormSeven.coordinate_edges
#print axioms Erdos714OddSquareNormSeven.polynomial_irreducible
#print axioms Erdos714OddSquareNormSeven.norm_edges
#print axioms Erdos714OddSquareNormSeven.powerBasisCopy
#print axioms Erdos714OddSquareNormSeven.not_free_of_irreducible
#print axioms Erdos714OddSquareNormSeven.seven_not_free

#print axioms Erdos714OddSquareNormSeven.irreducible_of_base_degree
#print axioms Erdos714OddSquareNormSeven.not_free_of_base_degree
#print axioms Erdos714OddSquareNormSeven.not_free_of_card

#print axioms Erdos714OddSquareNormSeven.nonsquare_family

#print axioms Erdos714OddSquareNormSeven.inversion_norm
