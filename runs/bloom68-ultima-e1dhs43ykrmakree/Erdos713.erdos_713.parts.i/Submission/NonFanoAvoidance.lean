import Submission.NonFano
import Submission.QuadrangleIdentity

/-!
# Non-Fano avoidance by orthogonality graphs in characteristic two

Development only: this construction gives forbidden-subgraph examples, not
an upper bound on the extremal number of the non-Fano graph.
-/

open Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Erdos713

private def pointRole (i : Fin 7) : Fin 16 := ⟨i, by omega⟩
private def lineRole (i : Fin 9) : Fin 16 := ⟨i + 7, by omega⟩

private theorem role_incidence : ∀ (i : Fin 9) (j : Fin 7),
    j ∈ homogeneousNonFanoLinePoints i ↔ nonFanoGraph.Adj (pointRole j) (lineRole i) := by
  decide

/-- Orthogonality of projectively distinct vectors over a characteristic-two
field excludes the specified non-Fano graph. This applies to ordinary subgraph
copies: no inducedness assumption is needed. -/
theorem nonFanoGraph_free_of_orthogonalRepresentation
    {K V : Type*} [Field K] [CharP K 2] (G : SimpleGraph V)
    (r : V → Fin 3 → K)
    (hr : ∀ u v, u ≠ v → r u ⨯₃ r v ≠ 0)
    (horth : ∀ ⦃u v⦄, G.Adj u v → r u ⬝ᵥ r v = 0) :
    nonFanoGraph.Free G := by
  rintro ⟨f⟩
  apply homogeneousNonFano_not_charTwo
    (fun i => r (f (pointRole i))) (fun i => r (f (lineRole i)))
  · intro i j hij
    apply hr
    intro he
    apply hij
    have h := congrArg Fin.val (f.injective he)
    exact Fin.ext h
  · intro i j hij
    apply hr
    intro he
    apply hij
    have h := congrArg Fin.val (f.injective he)
    apply Fin.ext
    dsimp [lineRole] at h
    omega
  · intro i j hij
    exact horth (f.toHom.map_adj ((role_incidence i j).mp hij))

/-- Canonical homogeneous points: `(0,0,1)`, `(0,1,c)`, and `(1,a,b)`. -/
abbrev PolarityPoint (K : Type*) := Option (K ⊕ (K × K))

def polarityVector {K : Type*} [Field K] : PolarityPoint K → Fin 3 → K
  | none => ![0, 0, 1]
  | some (.inl c) => ![0, 1, c]
  | some (.inr (a, b)) => ![1, a, b]

/-- Distinct canonical points are not proportional. -/
theorem polarityVector_cross_ne_zero {K : Type*} [Field K]
    (u v : PolarityPoint K) (h : u ≠ v) :
    polarityVector u ⨯₃ polarityVector v ≠ 0 := by
  intro hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  cases u with
  | none =>
    cases v with
    | none => exact h rfl
    | some v => cases v <;>
        simp [polarityVector, cross_apply] at h0 h1 h2
  | some u =>
    cases v with
    | none => cases u <;>
        simp [polarityVector, cross_apply] at h0 h1 h2
    | some v =>
      cases u <;> cases v <;>
        simp [polarityVector, cross_apply, sub_eq_zero] at h0 h1 h2
      · exact h (by simp [h0])
      · exact h (by simpa [Prod.ext_iff] using And.intro h2.symm h1)

/-- The loopless orthogonal-polarity graph in canonical coordinates. -/
def polarityGraph (K : Type*) [Field K] : SimpleGraph (PolarityPoint K) where
  Adj u v := u ≠ v ∧ polarityVector u ⬝ᵥ polarityVector v = 0
  symm := by intro u v h; exact ⟨h.1.symm, by simpa [dotProduct_comm] using h.2⟩
  loopless := by intro u h; exact h.1 rfl

instance {K : Type*} [Field K] [DecidableEq K] : DecidableRel (polarityGraph K).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Every characteristic-two member of the family is non-Fano-free. -/
theorem nonFanoGraph_free_polarityGraph (K : Type*) [Field K] [CharP K 2] :
    nonFanoGraph.Free (polarityGraph K) :=
  nonFanoGraph_free_of_orthogonalRepresentation _ polarityVector
    polarityVector_cross_ne_zero (by intro u v h; exact h.2)

/-- The projective-plane vertex count, obtained directly from the canonical coordinates. -/
theorem card_polarityPoint (K : Type*) [Field K] [Fintype K] :
    Fintype.card (PolarityPoint K) = (Fintype.card K)^2 + Fintype.card K + 1 := by
  simp only [PolarityPoint, Fintype.card_option, Fintype.card_sum, Fintype.card_prod]
  ring


open scoped BigOperators

private theorem affine_zero_iff {K : Type*} [Field K]
    (a b x : K) (ha : a ≠ 0) : a * x + b = 0 ↔ x = -b / a := by
  rw [eq_div_iff ha]
  constructor <;> intro h <;> linear_combination h

/-- Every projective point has exactly `q+1` orthogonal projective points;
this count includes a possible self-incidence. -/
theorem polarity_orthogonal_count (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (u : PolarityPoint K) :
    ∑ v : PolarityPoint K,
      (if polarityVector u ⬝ᵥ polarityVector v = 0 then 1 else 0 : ℕ) =
      Fintype.card K + 1 := by
  classical
  cases u with
  | none =>
    rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [polarityVector, Nat.add_comm]
  | some u =>
    cases u with
    | inl c =>
      have hP : (∑ x : K × K, if x.1 + c * x.2 = 0 then 1 else 0 : ℕ) =
          Fintype.card K := by
        rw [Fintype.sum_prod_type_right]
        simp [add_eq_zero_iff_eq_neg]
      have hL : (∑ d : K, if 1 + c * d = 0 then 1 else 0 : ℕ) =
          if c = 0 then 0 else 1 := by
        by_cases hc : c = 0
        · simp [hc]
        · have heq : ∀ d : K, 1 + c * d = 0 ↔ d = -1 / c := by
            intro d
            rw [add_comm]
            exact affine_zero_iff c 1 d hc
          simp [heq, hc]
      simp only [Fintype.sum_option, Fintype.sum_sum_type]
      simp only [polarityVector, vec3_dotProduct]
      dsimp
      simp only [one_mul, add_zero, zero_add, mul_one, mul_zero]
      rw [hP, hL]
      split_ifs <;> omega
    | inr ab =>
      rcases ab with ⟨a, b⟩
      by_cases hb : b = 0
      · subst b
        by_cases ha : a = 0
        · subst a
          rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
          simp [polarityVector, Nat.add_comm]
        · have heq : ∀ d : K, 1 + a * d = 0 ↔ d = -1 / a := by
            intro d
            rw [add_comm]
            exact affine_zero_iff a 1 d ha
          rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
          simp [polarityVector, heq, ha, Nat.add_comm]
      · have hL : (∑ c : K, if a + b * c = 0 then 1 else 0 : ℕ) = 1 := by
          have heq : ∀ c : K, a + b * c = 0 ↔ c = -a / b := by
            intro c
            rw [add_comm]
            exact affine_zero_iff b a c hb
          simp [heq]
        have hP : (∑ x : K × K, if 1 + a * x.1 + b * x.2 = 0 then 1 else 0 : ℕ) =
            Fintype.card K := by
          rw [Fintype.sum_prod_type]
          have heq : ∀ d e : K, 1 + a * d + b * e = 0 ↔ e = -(1 + a * d) / b := by
            intro d e
            rw [add_comm (1 + a * d)]
            exact affine_zero_iff b (1 + a * d) e hb
          simp [heq]
        simp only [Fintype.sum_option, Fintype.sum_sum_type]
        simp only [polarityVector, vec3_dotProduct]
        dsimp
        simp only [add_zero, zero_add, mul_one, mul_zero]
        rw [hL, hP]
        simp [hb, Nat.add_comm]


/-- Exactly `q+1` points are absolute points of the characteristic-two polarity. -/
theorem polarity_absolute_count (K : Type*) [Field K] [CharP K 2]
    [Fintype K] [DecidableEq K] :
    ∑ u : PolarityPoint K,
      (if polarityVector u ⬝ᵥ polarityVector u = 0 then 1 else 0 : ℕ) =
      Fintype.card K + 1 := by
  classical
  have hL : ∀ c : K, 1 + c * c = 0 ↔ c = 1 := by
    intro c
    have hs : (1 + c)^2 = 1 + c * c := by
      rw [CharTwo.add_sq]
      simp [pow_two]
    rw [← hs, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), CharTwo.add_eq_zero, eq_comm]
  have hP : ∀ a b : K, 1 + a * a + b * b = 0 ↔ b = 1 + a := by
    intro a b
    have hs : (1 + a + b)^2 = 1 + a * a + b * b := by
      rw [CharTwo.add_sq, CharTwo.add_sq]
      simp [pow_two]
    rw [← hs, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), CharTwo.add_eq_zero, eq_comm]
  rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [polarityVector, ← add_assoc, hL, hP, Nat.add_comm]

/-- Removing the possible loop subtracts exactly the absolute-point indicator. -/
theorem polarity_degree_add_absolute (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (u : PolarityPoint K) :
    (polarityGraph K).degree u +
      (if polarityVector u ⬝ᵥ polarityVector u = 0 then 1 else 0 : ℕ) =
      Fintype.card K + 1 := by
  classical
  have hdeg : (polarityGraph K).degree u =
      ∑ v : PolarityPoint K, (if (polarityGraph K).Adj u v then 1 else 0 : ℕ) := by
    simpa using (polarityGraph K).degree_eq_sum_if_adj (R := ℕ) u
  rw [hdeg]
  calc
    _ = ∑ v : PolarityPoint K,
        ((if (polarityGraph K).Adj u v then 1 else 0 : ℕ) +
          if v = u then (if polarityVector u ⬝ᵥ polarityVector u = 0 then 1 else 0) else 0) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ v : PolarityPoint K,
        (if polarityVector u ⬝ᵥ polarityVector v = 0 then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v = u
      · subst v
        simp [polarityGraph]
      · by_cases ho : polarityVector u ⬝ᵥ polarityVector v = 0 <;>
          simp [polarityGraph, hv, Ne.symm hv, ho]
    _ = _ := polarity_orthogonal_count K u

/-- The exact edge count, with the factor two avoiding natural-number division. -/
theorem polarity_twice_edge_count (K : Type*) [Field K] [CharP K 2]
    [Fintype K] [DecidableEq K] :
    2 * (polarityGraph K).edgeFinset.card =
      Fintype.card K * (Fintype.card K + 1)^2 := by
  have h : (∑ u : PolarityPoint K, (polarityGraph K).degree u) +
      (∑ u : PolarityPoint K,
        if polarityVector u ⬝ᵥ polarityVector u = 0 then 1 else 0 : ℕ) =
      ∑ _u : PolarityPoint K, (Fintype.card K + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact polarity_degree_add_absolute K u
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, polarity_absolute_count] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_polarityPoint] at h
  nlinarith [h]

/-- The usual finite-field polarity-graph edge count. -/
theorem polarity_edge_count (K : Type*) [Field K] [CharP K 2]
    [Fintype K] [DecidableEq K] :
    (polarityGraph K).edgeFinset.card =
      Fintype.card K * (Fintype.card K + 1)^2 / 2 := by
  have h := polarity_twice_edge_count K
  omega


/-- A lower bound for the ordinary extremal number, not a family-restricted variant. -/
theorem nonFano_extremal_lower_finiteField (K : Type*) [Field K] [CharP K 2]
    [Fintype K] :
    Fintype.card K * (Fintype.card K + 1)^2 / 2 ≤
      SimpleGraph.extremalNumber ((Fintype.card K)^2 + Fintype.card K + 1) nonFanoGraph := by
  classical
  have h := SimpleGraph.card_edgeFinset_le_extremalNumber (nonFanoGraph_free_polarityGraph K)
  rwa [card_polarityPoint, polarity_edge_count] at h

/-- The construction exists at every positive power of two. -/
theorem nonFano_extremal_lower_power_two (k : ℕ) (hk : k ≠ 0) :
    2^k * (2^k + 1)^2 / 2 ≤
      SimpleGraph.extremalNumber ((2^k)^2 + 2^k + 1) nonFanoGraph := by
  letI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 k) = 2^k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 k hk
  simpa only [hc] using nonFano_extremal_lower_finiteField (GaloisField 2 k)

end Erdos713

#print axioms Erdos713.nonFanoGraph_free_of_orthogonalRepresentation
#print axioms Erdos713.polarityVector_cross_ne_zero
#print axioms Erdos713.nonFanoGraph_free_polarityGraph
#print axioms Erdos713.card_polarityPoint

#print axioms Erdos713.polarity_orthogonal_count

#print axioms Erdos713.polarity_absolute_count
#print axioms Erdos713.polarity_degree_add_absolute
#print axioms Erdos713.polarity_twice_edge_count
#print axioms Erdos713.polarity_edge_count

#print axioms Erdos713.nonFano_extremal_lower_finiteField
#print axioms Erdos713.nonFano_extremal_lower_power_two
