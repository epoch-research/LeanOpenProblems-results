import Submission.FourMatchingCompletions
import Submission.ShiftedTwoVertexCuts

/-!
Adaptive decomposition across four odd terminals when all terminal pairs are
absent from the two sides. All three parity completions are used as needed;
there is no bounded-cost assertion for an arbitrary fixed pairing.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

omit [Fintype V] in
lemma support_sup_eq (A B : SimpleGraph V) : (A ⊔ B).support = A.support ∪ B.support := by
  ext x
  simp only [mem_support,sup_adj,Set.mem_union]
  aesop

noncomputable def fourMatching (t : Fin 4 → V) (i : Fin 3) : SimpleGraph V :=
  edge (t 0) (t (firstEnd i)) ⊔ edge (t (secondStart i)) (t (secondEnd i))

omit [Fintype V] in
lemma fourMatching_edges (t : Fin 4 → V) (ht : Function.Injective t) (i : Fin 3) :
    (fourMatching t i).edgeSet = {s(t 0,t (firstEnd i)),s(t (secondStart i),t (secondEnd i))} := by
  have hn1 : (0 : Fin 4) ≠ firstEnd i := by fin_cases i <;> decide
  have h1 : t 0 ≠ t (firstEnd i) := fun h => hn1 (ht h)
  have hn2 : secondStart i ≠ secondEnd i := by fin_cases i <;> decide
  have h2 : t (secondStart i) ≠ t (secondEnd i) := fun h => hn2 (ht h)
  rw [fourMatching,edgeSet_sup,edge_edgeSet_of_ne h1,edge_edgeSet_of_ne h2]
  exact Set.singleton_union

omit [Fintype V] in
lemma fourMatching_support (t : Fin 4 → V) (ht : Function.Injective t) (i : Fin 3) :
    (fourMatching t i).support = Set.range t := by
  have hn1 : (0 : Fin 4) ≠ firstEnd i := by fin_cases i <;> decide
  have h1 : t 0 ≠ t (firstEnd i) := fun h => hn1 (ht h)
  have hn2 : secondStart i ≠ secondEnd i := by fin_cases i <;> decide
  have h2 : t (secondStart i) ≠ t (secondEnd i) := fun h => hn2 (ht h)
  rw [fourMatching,support_sup_eq,TwoTerminalGluing.support_edge_eq h1,
    TwoTerminalGluing.support_edge_eq h2,four_terminal_range]
  fin_cases i <;> ext x <;>
    simp only [firstEnd,secondStart,secondEnd,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto

lemma fourMatching_degree (t : Fin 4 → V) (ht : Function.Injective t) (i : Fin 3) (x : V) :
    (fourMatching t i).degree x = if x ∈ Set.range t then 1 else 0 := by
  have hn1 : (0 : Fin 4) ≠ firstEnd i := by fin_cases i <;> decide
  have h1 : t 0 ≠ t (firstEnd i) := fun h => hn1 (ht h)
  have hn2 : secondStart i ≠ secondEnd i := by fin_cases i <;> decide
  have h2 : t (secondStart i) ≠ t (secondEnd i) := fun h => hn2 (ht h)
  have hne : s(t 0,t (firstEnd i)) ≠ s(t (secondStart i),t (secondEnd i)) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · have hh := ht h.1
      fin_cases i <;> simp [secondStart] at hh
    · have hh := ht h.1
      fin_cases i <;> simp [secondEnd] at hh
  have hd : Disjoint (edge (t 0) (t (firstEnd i))).edgeSet
      (edge (t (secondStart i)) (t (secondEnd i))).edgeSet := by
    rw [edge_edgeSet_of_ne h1,edge_edgeSet_of_ne h2,Set.disjoint_singleton]
    exact hne
  have hh := degree_sup_of_edge_disjoint _ _ hd x
  have hd1 := TwoTerminalGluing.degree_edge_eq h1 x
  have hd2 := TwoTerminalGluing.degree_edge_eq h2 x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hd1 hd2 ⊢
  change Nat.card ((edge (t 0) (t (firstEnd i)) ⊔
    edge (t (secondStart i)) (t (secondEnd i))).neighborSet x) = _
  rw [hh,hd1,hd2]
  by_cases hx : x ∈ Set.range t
  · rw [if_pos hx]
    obtain ⟨j,rfl⟩ := hx
    fin_cases i <;> fin_cases j <;> simp [firstEnd,secondStart,secondEnd,ht.eq_iff]
  · rw [if_neg hx]
    have hn : ∀ j, x ≠ t j := fun j h => hx ⟨j,h.symm⟩
    simp only [hn,false_or,if_false,Nat.zero_add]

lemma four_matching_completion (A : SimpleGraph V) (t : Fin 4 → V) (ht : Function.Injective t)
    (hodd : ∀ x, Even (A.degree x) ↔ x ∉ Set.range t)
    (hno : ∀ i j : Fin 4, ¬ A.Adj (t i) (t j)) (i : Fin 3) :
    (∀ x, Even ((A ⊔ fourMatching t i).degree x)) ∧
      (A ⊔ fourMatching t i).support ⊆ A.support := by
  have hd : Disjoint A.edgeSet (fourMatching t i).edgeSet := by
    rw [fourMatching_edges t ht i]
    apply Set.disjoint_left.mpr
    intro e he hm
    rcases hm with rfl | hm
    · exact hno 0 (firstEnd i) he
    · have hm' : e = s(t (secondStart i),t (secondEnd i)) := hm
      apply hno (secondStart i) (secondEnd i)
      exact (show s(t (secondStart i),t (secondEnd i)) ∈ A.edgeSet from hm' ▸ he)
  constructor
  · intro x
    have hh := degree_sup_of_edge_disjoint _ _ hd x
    have hm := fourMatching_degree t ht i x
    have hx := hodd x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hm hx ⊢
    rw [hh,hm]
    by_cases ht' : x ∈ Set.range t
    · rw [if_pos ht',Nat.even_add_one,hx]
      exact not_not.mpr ht'
    · rw [if_neg ht',Nat.add_zero,hx]
      exact ht'
  · rw [support_sup_eq,fourMatching_support t ht i]
    apply Set.union_subset le_rfl
    intro x hx
    apply (A.degree_pos_iff_mem_support x).mp
    by_contra! hz
    have hzero : A.degree x = 0 := by omega
    have hev : Even (A.degree x) := by rw [hzero]; decide
    exact (hodd x).mp hev hx

/-- The routing alternatives follow from a bound for all even graphs on the
side's support. The added terminal matching does not enlarge that support. -/
lemma routing_of_even_support_bounds {G A : SimpleGraph V} (hAG : A ≤ G)
    (t : Fin 4 → V) (ht : Function.Injective t)
    (hodd : ∀ x, Even (A.degree x) ↔ x ∉ Set.range t)
    (hno : ∀ i j : Fin 4, ¬ A.Adj (t i) (t j)) (k : ℕ)
    (hb : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → ExactVertexSmoothing.HasPieceBound k X) :
    FourRoutingAlternatives G A t k := by
  apply routing_alternatives_of_completions t ht hAG (fun i => A ⊔ fourMatching t i) k
  · intro i
    rw [edgeSet_sup,fourMatching_edges t ht i]
  · intro i
    exact ⟨hno 0 (firstEnd i),hno (secondStart i) (secondEnd i)⟩
  · intro i
    have hh := four_matching_completion A t ht hodd hno i
    exact hb _ hh.2 (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.1 x)

/-- A genuine four-odd-terminal gluing theorem with a fixed additive cost.
The independent-terminal hypothesis makes every correction matching a set
of new edges. It is not omitted or inferred from connectivity. -/
lemma four_odd_terminal_separation {G A B : SimpleGraph V} (t : Fin 4 → V)
    (ht : Function.Injective t) (hAG : A ≤ G) (hBG : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ Set.range t)
    (hoddA : ∀ x, Even (A.degree x) ↔ x ∉ Set.range t)
    (hoddB : ∀ x, Even (B.degree x) ↔ x ∉ Set.range t)
    (hnoA : ∀ i j : Fin 4, ¬ A.Adj (t i) (t j))
    (hnoB : ∀ i j : Fin 4, ¬ B.Adj (t i) (t j)) (kA kB : ℕ)
    (hbA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → ExactVertexSmoothing.HasPieceBound kA X)
    (hbB : ∀ X : SimpleGraph V, X.support ⊆ B.support →
      (∀ x, Even (X.degree x)) → ExactVertexSmoothing.HasPieceBound kB X) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ kA+kB+4 := by
  exact adaptive_four_routing ht hd hi hcover kA kB
    (routing_of_even_support_bounds hAG t ht hoddA hnoA kA hbA)
    (routing_of_even_support_bounds hBG t ht hoddB hnoB kB hbB)

end Erdos184.TerminalRouting
