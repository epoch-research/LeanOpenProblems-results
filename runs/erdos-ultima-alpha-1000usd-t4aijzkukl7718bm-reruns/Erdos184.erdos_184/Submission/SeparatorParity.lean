import Submission.ThreeVertexSeparation

/-! Odd side degrees for an even graph separated across at most four vertices. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteTerminalGluing
open TwoTerminalGluing
variable {V : Type*} [Fintype V]

lemma odd_side_set {G A B : SimpleGraph V} (S : Set V)
    (heG : ∀ x, Even (G.degree x))
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hv : A.support ∩ B.support ⊆ S) :
    ∃ T : Set V, T ⊆ S ∧ Even T.ncard ∧
      (∀ x, Even (A.degree x) ↔ x ∉ T) ∧
      (∀ x, Even (B.degree x) ↔ x ∉ T) := by
  have heq : A ⊔ B = G := edgeSet_injective (by rw [edgeSet_sup,hu])
  have hpar (x : V) : Even (A.degree x) ↔ Even (B.degree x) := by
    have hh := degree_sup_of_edge_disjoint A B hd x
    have hx := heG x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,heq] at hh hx ⊢
    rw [hh] at hx
    exact Nat.even_add.mp hx
  have hout (x : V) (hxS : x ∉ S) : Even (A.degree x) := by
    by_cases hx : x ∈ A.support
    · have hxB : x ∉ B.support := fun hy => hxS (hv ⟨hx,hy⟩)
      have hh := degree_eq_of_other_unsupported hu x hxB
      have hx := heG x
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hx ⊢
      rwa [hh]
    · rw [(A.degree_eq_zero_iff_notMem_support x).mpr hx]
      decide
  let F : Finset V := Finset.univ.filter (fun x => Odd (A.degree x))
  have hF : ∀ x, x ∈ F ↔ ¬Even (A.degree x) := by
    intro x
    simp only [F,Finset.mem_filter,Finset.mem_univ,true_and,Nat.not_even_iff_odd]
  refine ⟨(F : Set V), ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hn
    exact (hF x).mp hx (hout x hn)
  · simpa only [Set.ncard_coe_finset] using A.even_card_odd_degree_vertices
  · intro x
    simp only [Finset.mem_coe,hF,not_not]
  · intro x
    simpa only [Finset.mem_coe,hF,not_not] using (hpar x).symm

/-- Four-terminal parity has exactly three possibilities: zero, two, or four
odd vertices. In the last case the entire separator is odd. -/
lemma parity_of_four_separation {G A B : SimpleGraph V} (S : Set V)
    (hS : S.ncard ≤ 4) (heG : ∀ x, Even (G.degree x))
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hv : A.support ∩ B.support ⊆ S) :
    ((∀ x, Even (A.degree x)) ∧ (∀ x, Even (B.degree x))) ∨
    (∃ a b : V, a ≠ b ∧
      (∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b) ∧
      (∀ x, Even (B.degree x) ↔ x ≠ a ∧ x ≠ b)) ∨
    (S.ncard = 4 ∧
      (∀ x, Even (A.degree x) ↔ x ∉ S) ∧
      (∀ x, Even (B.degree x) ↔ x ∉ S)) := by
  obtain ⟨T,hTS,hev,hA,hB⟩ := odd_side_set S heG hd hu hv
  have hcard := (Set.ncard_le_ncard hTS).trans hS
  have hh : T.ncard = 0 ∨ T.ncard = 2 ∨ T.ncard = 4 := by
    obtain ⟨k,hk⟩ := hev
    omega
  rcases hh with hz | ht | hf
  · have hT : T = ∅ := (Set.ncard_eq_zero (Set.toFinite T)).mp hz
    left
    exact ⟨fun x => (hA x).mpr (by simp [hT]),fun x => (hB x).mpr (by simp [hT])⟩
  · right; left
    obtain ⟨a,b,hab,hTab⟩ := Set.ncard_eq_two.mp ht
    refine ⟨a,b,hab,?_,?_⟩
    · simpa only [hTab,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using hA
    · simpa only [hTab,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using hB
  · have hT : T = S := Set.eq_of_subset_of_ncard_le hTS (by omega)
    right; right
    exact ⟨by simpa only [hT] using hf, by simpa only [hT] using hA,by simpa only [hT] using hB⟩

lemma enumerate_four_set (S : Set V) (hS : S.ncard = 4) :
    ∃ t : Fin 4 → V, Function.Injective t ∧ Set.range t = S := by
  have hc : Fintype.card S = 4 := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hS
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      exact ⟨i,congrArg Subtype.val hi⟩

end Erdos184.FiniteTerminalGluing
