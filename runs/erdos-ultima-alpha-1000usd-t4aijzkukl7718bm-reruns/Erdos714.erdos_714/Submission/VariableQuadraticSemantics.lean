import Submission.VariableQuadraticCertificate
import Submission.OrdinarySquarePoints
import Submission.TranslatedNormFibers

/-!
A finite-field specialization of the varying quadratic-form certificate.
Both extension parameters, the Frobenius involution, and the actual
Algebra.norm interpretation are proved here. This is not a disproof of
Erdős 714: it excludes only the displayed candidate graph at q=27.
-/
noncomputable section
open Polynomial SimpleGraph
namespace Erdos714VariableQuadraticSemantics
open Erdos714OrdinarySquarePoints (K z z_spec card_K)
open Erdos714VariableQuadratic

def extensionPolynomial : K[X] := X^2+1

lemma extension_monic : extensionPolynomial.Monic := by
  unfold extensionPolynomial
  monicity!

lemma extension_degree : extensionPolynomial.natDegree = 2 := by
  unfold extensionPolynomial
  compute_degree!

lemma extension_irreducible : Irreducible extensionPolynomial := by
  have hns : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, card_K]
    norm_num
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [extension_degree]; decide
  · intro x hx
    have hx' : x^2+1 = 0 := by simpa [extensionPolynomial, IsRoot.def] using hx
    apply hns
    exact ⟨x,by linear_combination -hx'⟩

instance : Fact (Irreducible extensionPolynomial) := ⟨extension_irreducible⟩
abbrev L := AdjoinRoot extensionPolynomial
instance : CharP L 3 := charP_of_injective_algebraMap (algebraMap K L).injective 3
instance : Fintype L :=
  Fintype.ofEquiv (Fin extensionPolynomial.natDegree → K)
    (AdjoinRoot.powerBasis extension_monic.ne_zero).basis.equivFun.symm.toEquiv

lemma card_L : Fintype.card L = 729 := by
  have h := Fintype.card_congr (AdjoinRoot.powerBasis extension_monic.ne_zero).basis.equivFun.toEquiv
  simpa [extension_degree, card_K] using h

def imaginaryUnit : L := AdjoinRoot.root extensionPolynomial
lemma imaginaryUnit_sq : imaginaryUnit^2 = -1 := by
  have h := AdjoinRoot.eval₂_root extensionPolynomial
  have hh : imaginaryUnit^2+1 = 0 := by simpa [extensionPolynomial, imaginaryUnit] using h
  linear_combination hh

def parameter : L := algebraMap K L (-z)
lemma parameter_spec : parameter^3-parameter+1 = 0 := by
  have h := congrArg (algebraMap K L) z_spec
  simp only [map_sub, map_pow, map_one, map_zero] at h
  unfold parameter
  rw [map_neg]
  linear_combination -h

def conjugation : L →+* L := (frobenius L 3)^3

lemma conjugation_apply (x : L) : conjugation x = x^27 := by
  change ((frobenius L 3)^3) x = x^27
  rw [RingHom.coe_pow, iterate_frobenius]
  norm_num

lemma conjugation_involutive : Function.Involutive conjugation := by
  intro x
  rw [conjugation_apply, conjugation_apply, ← pow_mul]
  simpa only [card_L] using FiniteField.pow_card x

lemma conjugation_coefficient (a : K) : conjugation (algebraMap K L a) = algebraMap K L a := by
  rw [conjugation_apply, ← map_pow]
  congr 1
  simpa only [card_K] using FiniteField.pow_card a

lemma conjugation_parameter : conjugation parameter = parameter := conjugation_coefficient _

lemma conjugation_imaginaryUnit : conjugation imaginaryUnit = -imaginaryUnit := by
  rw [conjugation_apply]
  calc
    imaginaryUnit^27 = (imaginaryUnit^2)^13*imaginaryUnit := by ring
    _ = -imaginaryUnit := by rw [imaginaryUnit_sq]; norm_num

/-- The product with the conjugate is the actual quadratic field norm. -/
lemma norm_semantics (x : L) :
    algebraMap K L (Algebra.norm K x) = Erdos714VariableQuadratic.norm conjugation x := by
  have hcard : Fintype.card L = Fintype.card K^2 := by rw [card_L,card_K]; norm_num
  have h := Erdos714TranslatedNorm.quadratic_norm_power hcard x
  simpa [Erdos714VariableQuadratic.norm, conjugation_apply, card_K, pow_succ, mul_comm] using h

def fieldRelation (x u : L) : Prop :=
  Algebra.norm K u ≠ 1 ∧ Algebra.norm K (x+u*x^27) = 1+(Algebra.norm K u)^2

def fieldGraph : SimpleGraph ((L × L) ⊕ (L × L)) where
  Adj a b := match a,b with
    | .inl x, .inr y => fieldRelation (x.1+y.1) (x.2+y.2)
    | .inr y, .inl x => fieldRelation (x.1+y.1) (x.2+y.2)
    | _,_ => False
  symm := by intro a b; cases a <;> cases b <;> exact id
  loopless := by intro a; cases a <;> exact not_false

lemma fieldRelation_iff (x u : L) : fieldRelation x u ↔ relation conjugation x u := by
  have hnorm (u : L) : Algebra.norm K u = 1 ↔ norm conjugation u = 1 := by
    rw [← (algebraMap K L).injective.eq_iff, norm_semantics, map_one]
  unfold fieldRelation relation
  simp only [ne_eq, hnorm]
  apply and_congr_right
  intro _
  rw [← (algebraMap K L).injective.eq_iff, norm_semantics, map_add, map_one, map_pow, norm_semantics]
  rw [conjugation_apply]

lemma graph_eq : fieldGraph = graph conjugation := by
  ext x y
  cases x <;> cases y <;> simp only [fieldGraph, graph, fieldRelation_iff]

/-- A closed, kernel-checked finite-field counterexample to this candidate. -/
theorem fieldGraph_not_free : ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free fieldGraph := by
  rw [graph_eq]
  exact cubic_parameter_not_free conjugation conjugation_involutive parameter imaginaryUnit
    parameter_spec conjugation_parameter imaginaryUnit_sq conjugation_imaginaryUnit

#print axioms extension_irreducible
#print axioms card_L
#print axioms conjugation_involutive
#print axioms norm_semantics
#print axioms fieldRelation_iff
#print axioms fieldGraph_not_free
end Erdos714VariableQuadraticSemantics
