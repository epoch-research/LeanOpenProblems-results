import FormalConjecturesUtil

/-!
# Finite reciprocity and template errors

These are purely finite combinatorial partial lemmas, not a resolution of the
Ostmann problem. Boolean values represent the two signs; `^^` is Boolean XOR.

A relation covering every distinct pair, with at most `k` outgoing incidences
per vertex, has at most `2 * k + 1` vertices. For an antisymmetric Boolean edge
array approximated by `R` templates up to a row orientation, vertices with the
same `(template, orientation XOR diagonal template value)` have at least one
error between every pair. There are `2 * R` such classes, giving the bound
`R * (4 * k + 2)`. Diagonal edges are unrestricted and are not counted as errors.
-/

open scoped BigOperators

namespace ReciprocityCombinatorics

/-- A directed relation covering every distinct pair and having at most `k`
outgoing incidences at each vertex has at most `2 * k + 1` vertices.
Both directions may hold; in particular, this applies to a tournament. -/
theorem card_le_two_mul_add_one_of_pair_cover
    {V : Type*} [DecidableEq V] (s : Finset V)
    (E : V → V → Prop) [DecidableRel E] (k : ℕ)
    (hcover : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → E i j ∨ E j i)
    (hdegree : ∀ i ∈ s, (s.filter (E i)).card ≤ k) :
    s.card ≤ 2 * k + 1 := by
  have hlocal (i : V) (hi : i ∈ s) :
      s.card - 1 ≤ (s.filter (E i)).card + (s.filter fun j => E j i).card := by
    have hsub : s.erase i ⊆ s.filter (E i) ∪ s.filter (fun j => E j i) := by
      intro j hj
      obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
      rcases hcover i hi j hjs hji.symm with hij | hji
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjs, hij⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjs, hji⟩)
    calc
      s.card - 1 = (s.erase i).card := (Finset.card_erase_of_mem hi).symm
      _ ≤ (s.filter (E i) ∪ s.filter (fun j => E j i)).card :=
        Finset.card_le_card hsub
      _ ≤ (s.filter (E i)).card + (s.filter fun j => E j i).card :=
        Finset.card_union_le _ _
  have htranspose :
      (∑ i ∈ s, (s.filter fun j => E j i).card) =
        ∑ i ∈ s, (s.filter (E i)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsum : (∑ i ∈ s, (s.filter (E i)).card) ≤ s.card * k := by
    calc
      (∑ i ∈ s, (s.filter (E i)).card) ≤ ∑ _i ∈ s, k :=
        Finset.sum_le_sum hdegree
      _ = s.card * k := by simp
  -- Count ordered distinct pairs. Each error can cover at most two of them.
  have hcount : s.card * (s.card - 1) ≤ s.card * (2 * k) := by
    calc
      s.card * (s.card - 1) = ∑ _i ∈ s, (s.card - 1) := by simp
      _ ≤ ∑ i ∈ s, ((s.filter (E i)).card + (s.filter fun j => E j i).card) :=
        Finset.sum_le_sum hlocal
      _ = 2 * (∑ i ∈ s, (s.filter (E i)).card) := by
        rw [Finset.sum_add_distrib, htranspose, two_mul]
      _ ≤ 2 * (s.card * k) := Nat.mul_le_mul_left 2 hsum
      _ = s.card * (2 * k) := by ring
  by_cases hz : s.card = 0
  · simp [hz]
  · have h := Nat.le_of_mul_le_mul_left hcount (Nat.pos_of_ne_zero hz)
    omega

/-- Two vertices of the same corrected template type cannot both predict their
mutual edge correctly when the actual edges have opposite signs. -/
theorem same_type_forces_mismatch
    {V : Type*} {R : ℕ}
    (edge : V → V → Bool) (f : Fin R → V → Bool)
    (template : V → Fin R) (orientation : V → Bool) {i j : V}
    (hantisymm : edge i j = !(edge j i))
    (htype :
      (template i, orientation i ^^ f (template i) i) =
        (template j, orientation j ^^ f (template j) j)) :
    edge i j ≠ (orientation i ^^ f (template i) j) ∨
      edge j i ≠ (orientation j ^^ f (template j) i) := by
  have ht : template i = template j := congrArg Prod.fst htype
  have hs : (orientation i ^^ f (template i) i) = (orientation j ^^ f (template j) j) :=
    congrArg Prod.snd htype
  have hcross (a b x y : Bool) (h : (a ^^ x) = (b ^^ y)) : (a ^^ y) = (b ^^ x) := by
    cases a <;> cases b <;> cases x <;> cases y <;> simp_all
  have hpred : (orientation i ^^ f (template i) j) = (orientation j ^^ f (template j) i) := by
    rw [← ht] at hs ⊢
    exact hcross _ _ _ _ hs
  by_cases hij : edge i j = (orientation i ^^ f (template i) j)
  · right
    intro hji
    have heq : edge i j = edge j i := hij.trans (hpred.trans hji.symm)
    exact Bool.self_ne_not _ (heq.symm.trans hantisymm)
  · exact Or.inl hij

/-- Finset version of the template bound. Each row has at most `k` mismatches
at *other* vertices of `s`. No hypothesis is imposed on diagonal edges. -/
theorem card_le_templates_of_row_errors
    {V : Type*} [DecidableEq V] {R k : ℕ} (s : Finset V)
    (edge : V → V → Bool) (f : Fin R → V → Bool)
    (template : V → Fin R) (orientation : V → Bool)
    (hantisymm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → edge i j = !(edge j i))
    (herrors : ∀ i ∈ s,
      (s.filter fun j => i ≠ j ∧
        edge i j ≠ (orientation i ^^ f (template i) j)).card ≤ k) :
    s.card ≤ R * (4 * k + 2) := by
  let vertexType : V → Fin R × Bool :=
    fun i => (template i, orientation i ^^ f (template i) i)
  let E : V → V → Prop :=
    fun i j => i ≠ j ∧ edge i j ≠ (orientation i ^^ f (template i) j)
  have hclass (c : Fin R × Bool) :
      (s.filter fun i => vertexType i = c).card ≤ 2 * k + 1 := by
    apply card_le_two_mul_add_one_of_pair_cover _ E k
    · intro i hi j hj hij
      obtain ⟨his, hic⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjs, hjc⟩ := Finset.mem_filter.mp hj
      have htype : vertexType i = vertexType j := hic.trans hjc.symm
      rcases same_type_forces_mismatch edge f template orientation
          (hantisymm i his j hjs hij) htype with hierr | hjerr
      · exact Or.inl ⟨hij, hierr⟩
      · exact Or.inr ⟨hij.symm, hjerr⟩
    · intro i hi
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      exact (Finset.card_le_card (Finset.filter_subset_filter (E i)
        (Finset.filter_subset _ _))).trans (herrors i his)
  calc
    s.card = ∑ c : Fin R × Bool, (s.filter fun i => vertexType i = c).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _c : Fin R × Bool, (2 * k + 1) :=
      Finset.sum_le_sum (fun c _ => hclass c)
    _ = R * (4 * k + 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, smul_eq_mul]
      ring

/-- Fintype version: an antisymmetric sign array that is within `k` off-diagonal
errors per row of `R` templates, up to orientation, has at most `R * (4 * k + 2)`
vertices. This also includes the empty-vertex and zero-template cases. -/
theorem fintype_card_le_templates_of_row_errors
    {V : Type*} [Fintype V] [DecidableEq V] {R k : ℕ}
    (edge : V → V → Bool) (f : Fin R → V → Bool)
    (template : V → Fin R) (orientation : V → Bool)
    (hantisymm : ∀ i j, i ≠ j → edge i j = !(edge j i))
    (herrors : ∀ i,
      (Finset.univ.filter fun j => i ≠ j ∧
        edge i j ≠ (orientation i ^^ f (template i) j)).card ≤ k) :
    Fintype.card V ≤ R * (4 * k + 2) := by
  simpa using card_le_templates_of_row_errors Finset.univ edge f template orientation
    (fun i _ j _ hij => hantisymm i j hij) (fun i _ => herrors i)

/-- Exception-set formulation: the predicted row need only agree outside a set
`errors i` of size at most `k`. The exception sets may contain the diagonal or
vertices outside `s`; neither causes a problem. -/
theorem card_le_templates_of_exception_sets
    {V : Type*} [DecidableEq V] {R k : ℕ} (s : Finset V)
    (edge : V → V → Bool) (f : Fin R → V → Bool)
    (template : V → Fin R) (orientation : V → Bool) (errors : V → Finset V)
    (hantisymm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → edge i j = !(edge j i))
    (hagrees : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → j ∉ errors i →
      edge i j = (orientation i ^^ f (template i) j))
    (herrors : ∀ i ∈ s, (errors i).card ≤ k) :
    s.card ≤ R * (4 * k + 2) := by
  apply card_le_templates_of_row_errors s edge f template orientation hantisymm
  intro i hi
  apply (Finset.card_le_card ?_).trans (herrors i hi)
  intro j hj
  obtain ⟨hjs, hij, herr⟩ := Finset.mem_filter.mp hj
  by_contra hjnot
  exact herr (hagrees i hi j hjs hij hjnot)

end ReciprocityCombinatorics
