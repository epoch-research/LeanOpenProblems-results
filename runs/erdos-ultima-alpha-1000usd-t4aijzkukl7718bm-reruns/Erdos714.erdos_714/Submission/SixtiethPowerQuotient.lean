import Submission.CrossPowerGrid

/-! A degree-twenty subfield excludes the cyclotomic degree-sixty power host
with weight support {1,2,3,4,5,6,30}. This is a uniform full-host obstruction,
not an arbitrary-thinning theorem or a solution of Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 3000000
namespace Erdos714SixtiethPower
open Erdos714WeightedPower

/-- The actual positive integral cyclotomic value, for q>=2. -/
def cyclo (q n : ℕ) : ℕ := (eval (q : ℤ) (cyclotomic n ℤ)).natAbs

lemma cyclo_cast (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    (cyclo q n : ℤ)=eval (q : ℤ) (cyclotomic n ℤ) :=
  Int.natAbs_of_nonneg (le_of_lt (cyclotomic_pos' n (by exact_mod_cast hq : (1 : ℤ)<q)))

lemma cyclo_pos (q : ℕ) (hq : 2 ≤ q) (n : ℕ) : 0 < cyclo q n := by
  apply Int.natAbs_pos.mpr
  exact (cyclotomic_pos' n (by exact_mod_cast hq : (1 : ℤ)<q)).ne'

lemma cyclo_product (q : ℕ) (hq : 2 ≤ q) (m : ℕ) (hm : 0 < m) :
    ∏ n ∈ m.divisors, cyclo q n=q^m-1 := by
  have h := congrArg (eval (q : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hm ℤ)
  simp only [eval_prod,eval_sub,eval_pow,eval_X,eval_one] at h
  have he : (∏ n ∈ m.divisors, cyclo q n)+1=q^m := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    simp_rw [cyclo_cast q hq]
    rw [h]
    ring
  omega

def exponentSupport : Finset ℕ := {10,12,15,20,60}
def weightSupport : Finset ℕ := {1,2,3,4,5,6,30}
def exponent (q : ℕ) : ℕ := ∏ n ∈ exponentSupport, cyclo q n
def weightSize (q : ℕ) : ℕ := ∏ n ∈ weightSupport, cyclo q n

def weightPolynomial : ℤ[X] := ∏ n ∈ weightSupport, cyclotomic n ℤ

lemma weight_degree : weightPolynomial.natDegree=20 := by
  rw [weightPolynomial,natDegree_prod _ _ (fun n _ => cyclotomic_ne_zero n ℤ)]
  simp_rw [natDegree_cyclotomic]
  decide

lemma weight_value (q : ℕ) (hq : 2 ≤ q) :
    (weightSize q : ℤ)=eval (q : ℤ) weightPolynomial := by
  rw [weightSize,weightPolynomial,eval_prod,Nat.cast_prod]
  apply prod_congr rfl
  intro n _
  exact cyclo_cast q hq n

lemma exponent_pos (q : ℕ) (hq : 2 ≤ q) : 0 < exponent q :=
  prod_pos (fun n _ => cyclo_pos q hq n)

lemma factorization (q : ℕ) (hq : 2 ≤ q) :
    q^60-1=exponent q*weightSize q := by
  rw [←cyclo_product q hq 60 (by decide),exponent,weightSize,
    ←prod_union (show Disjoint exponentSupport weightSupport by decide)]
  congr 1
  decide

/-- The degree-twenty restriction, not the full degree-sixty field, gives
this sufficient modulus. Cyclotomic evaluations are not assumed coprime. -/
lemma subfield_modulus_divides (q : ℕ) (hq : 2 ≤ q) :
    q^20-1 ∣ exponent q*Erdos714CrossPowerGrid.modulus q := by
  refine ⟨cyclo q 1*cyclo q 12*cyclo q 15*cyclo q 60,?_⟩
  rw [Erdos714CrossPowerGrid.modulus,←cyclo_product q hq 20 (by decide),
    ←cyclo_product q hq 4 (by decide),←cyclo_product q hq 5 (by decide)]
  have h20 : (20 : ℕ).divisors={1,2,4,5,10,20} := by decide
  have h4 : (4 : ℕ).divisors={1,2,4} := by decide
  have h5 : (5 : ℕ).divisors={1,5} := by decide
  rw [h20,h4,h5]
  norm_num only [exponent,exponentSupport,prod_insert,prod_singleton,
    mem_insert,mem_singleton,or_false,or_self,not_false_eq_true]
  ring

section Counts
variable {E : Type*} [Field E] [Fintype E]

lemma weight_cardinality (q : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^60) :
    Fintype.card (Weight E (exponent q))=weightSize q := by
  rw [weight_card,hE,factorization q hq,Nat.gcd_mul_right_left]
  exact Nat.mul_div_cancel_left _ (exponent_pos q hq)

lemma vertex_cardinality (q : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^60) :
    Fintype.card ((E × Weight E (exponent q)) ⊕ (E × Weight E (exponent q)))=
      2*q^60*weightSize q := by
  simp only [Fintype.card_sum,Fintype.card_prod,weight_cardinality q hq hE,hE]
  ring

lemma edge_cardinality (q : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^60) :
    (graph (powerMap E (exponent q))).edgeFinset.card=
      q^60*weightSize q*(q^60-1) := by
  rw [edge_count,weight_cardinality q hq hE,hE]
end Counts

section Galois
variable (p k : ℕ) [Fact p.Prime]
local instance (n : ℕ) : Fintype (GaloisField p n) := Fintype.ofFinite _

lemma galois_card (n : ℕ) (hn : n ≠ 0) : Fintype.card (GaloisField p n)=p^n := by
  rw [Fintype.card_eq_nat_card,GaloisField.card p n hn]

def baseEmbedding (hk : k ≠ 0) : GaloisField p k →ₐ[ZMod p] GaloisField p (20*k) := by
  apply Classical.choice
  apply FiniteField.nonempty_algHom_of_finrank_dvd
  rw [GaloisField.finrank p hk,GaloisField.finrank p (by omega : 20*k ≠ 0)]
  exact ⟨20,by ring⟩

def ambientEmbedding (hk : k ≠ 0) :
    GaloisField p (20*k) →ₐ[ZMod p] GaloisField p (60*k) := by
  apply Classical.choice
  apply FiniteField.nonempty_algHom_of_finrank_dvd
  rw [GaloisField.finrank p (by omega : 20*k ≠ 0),
    GaloisField.finrank p (by omega : 60*k ≠ 0)]
  exact ⟨3,by ring⟩

lemma base_degree (hk : k ≠ 0) :
    letI : Algebra (GaloisField p k) (GaloisField p (20*k)) :=
      (baseEmbedding p k hk).toRingHom.toAlgebra
    Module.finrank (GaloisField p k) (GaloisField p (20*k))=20 := by
  letI : Algebra (GaloisField p k) (GaloisField p (20*k)) :=
    (baseEmbedding p k hk).toRingHom.toAlgebra
  have hq : 2 ≤ p^k := by
    rw [←galois_card p k hk]
    exact Fintype.one_lt_card
  have he := Module.card_eq_pow_finrank (K := GaloisField p k) (V := GaloisField p (20*k))
  rw [galois_card p k hk,galois_card p (20*k) (by omega)] at he
  have hpw : p^(20*k)=(p^k)^20 := by rw [←pow_mul]; congr 1; ring
  rw [hpw] at he
  exact (Nat.pow_right_injective hq he).symm

/-- Every prime characteristic and every positive extension parameter are
included; the actual finite-field embeddings are part of the proof. -/
theorem not_free (hk : k ≠ 0) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (powerMap (GaloisField p (60*k)) (exponent (p^k)))) := by
  letI : Algebra (GaloisField p k) (GaloisField p (20*k)) :=
    (baseEmbedding p k hk).toRingHom.toAlgebra
  have hq : 2 ≤ p^k := by rw [←galois_card p k hk]; exact Fintype.one_lt_card
  have hd : Fintype.card (GaloisField p (20*k))-1 ∣
      exponent (p^k)*Erdos714CrossPowerGrid.modulus (Fintype.card (GaloisField p k)) := by
    rw [galois_card p (20*k) (by omega),galois_card p k hk]
    have hpw : p^(20*k)=(p^k)^20 := by rw [←pow_mul]; congr 1; ring
    rw [hpw]
    exact subfield_modulus_divides (p^k) hq
  have hsmall := Erdos714CrossPowerGrid.finite_not_free
    (base_degree p k hk) (exponent (p^k)) hd
  intro hfree
  apply hsmall
  rintro ⟨c⟩
  exact hfree ⟨(powerSubfieldCopy (exponent (p^k)) (ambientEmbedding p k hk).toRingHom).comp c⟩
end Galois
end Erdos714SixtiethPower
#print axioms Erdos714SixtiethPower.cyclo_product
#print axioms Erdos714SixtiethPower.weight_degree
#print axioms Erdos714SixtiethPower.factorization
#print axioms Erdos714SixtiethPower.subfield_modulus_divides
#print axioms Erdos714SixtiethPower.weight_cardinality
#print axioms Erdos714SixtiethPower.vertex_cardinality
#print axioms Erdos714SixtiethPower.edge_cardinality
#print axioms Erdos714SixtiethPower.not_free
