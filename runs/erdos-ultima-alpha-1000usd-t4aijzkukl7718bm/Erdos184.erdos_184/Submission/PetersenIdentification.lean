import Submission.PetersenIdentificationData

/-! A degree-two vertex-identification obstruction, not a disproof of Erdos 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PetersenIdentification
open Critical EvenCore
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

lemma number_upper : number graph ≤ 3 := by
  let P : Fin 3 → graph.Subgraph := ![cycle0.toSubgraph,cycle1.toSubgraph,cycle2.toSubgraph]
  let E : Fin 3 → Finset (Sym2 (Fin 25)) := ![cycle0.edges.toFinset,cycle1.edges.toFinset,cycle2.edges.toFinset]
  have hp : ∀ i : Fin 3, IsCycleOrEdge (P i).coe := by
    intro i
    fin_cases i
    all_goals apply Or.inl
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle0_cycle
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle1_cycle
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle2_cycle
  have hd : IsDecomposition graph (Finset.univ.image P) := by
    apply Compression.finite_family_decomposition P E
    · intro i
      fin_cases i <;> ext e <;> simp [P,E]
    · intro i j hne
      fin_cases i <;> fin_cases j <;>
        first | exact (hne rfl).elim |
          simp [E, List.disjoint_toFinset_iff_disjoint, cycle0, cycle1, cycle2, Sym2.eq_iff]
    · intro a b
      change graph.Adj a b ↔ ∃ i : Fin 3, s(a,b) ∈ E i
      simp only [Fin.exists_fin_succ, E, List.mem_toFinset]
      revert b
      fin_cases a <;> decide +kernel
  have hb := number_le (Finset.univ.image P) (by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hp i) hd
  have hn : (Finset.univ.image P).card ≤ 3 :=
    (Finset.card_image_le).trans (by simp)
  omega

lemma number_three : number graph = 3 := by
  have hb := StarCore.number_degree_bound graph 0
  have hd := degree_zero
  have hu := number_upper
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb hd
  rw [hd] at hb
  omega

def square : graph.Walk 1 1 :=
  .cons adj_1_13 (.cons adj_13_2 (.cons adj_2_22 (.cons adj_22_1 (.nil))))
lemma square_cycle : square.IsCycle := by
  simp [square, Walk.isCycle_def, Walk.isTrail_def]

lemma not_critical : ¬ CycleCritical graph := by
  intro hc
  have hh := CriticalSaturation.cycle_hits_saturated hc 0 (by
    have hd := degree_zero
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd ⊢
    rw [hd, number_three])
  have hs := hh 1 square square_cycle
  have hn : (0 : Fin 25) ∉ square.support := by decide +kernel
  exact hn hs

lemma not_minimal : ¬ EvenMinimal graph :=
  fun h => not_critical (h.cycleCritical (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using even v))

def quotient : DoublePetersenGraph.Vertex → Fin 25
  | .inl v => ⟨v.val, by omega⟩
  | .inr (e,b) => if b then ![23,24,14,22,21,11,19,10,16,20,18,13,15,17,12] e else ⟨10 + e.val, by omega⟩

instance : DecidableRel DoublePetersenGraph.graph.Adj := by
  unfold DoublePetersenGraph.graph
  infer_instance

lemma quotient_surjective : Function.Surjective quotient := by decide +kernel
lemma quotient_hom : ∀ x y, DoublePetersenGraph.graph.Adj x y →
    graph.Adj (quotient x) (quotient y) := by decide +kernel
lemma quotient_edge_surjective : ∀ a b, graph.Adj a b →
    ∃ x y, DoublePetersenGraph.graph.Adj x y ∧ quotient x = a ∧ quotient y = b := by
  intro a
  fin_cases a <;> decide +kernel
lemma private_degree : ∀ e : DoublePetersen.Edge,
    DoublePetersenGraph.graph.degree (.inr e) = 2 := by
  rintro ⟨e,b⟩
  fin_cases e <;> cases b <;> decide +kernel
lemma identified_private : ∀ x y, quotient x = quotient y → x ≠ y →
    (∃ e, x = Sum.inr e) ∧ (∃ e, y = Sum.inr e) := by decide +kernel
lemma identified_degree_two (x y : DoublePetersenGraph.Vertex)
    (h : quotient x = quotient y) (hne : x ≠ y) :
    DoublePetersenGraph.graph.degree x = 2 ∧ DoublePetersenGraph.graph.degree y = 2 := by
  obtain ⟨⟨e,rfl⟩,⟨f,rfl⟩⟩ := identified_private x y h hne
  exact ⟨private_degree e,private_degree f⟩

lemma obstruction :
    CycleCritical DoublePetersenGraph.graph ∧
    number DoublePetersenGraph.graph = 5 ∧
    (∀ v, Even (graph.degree v)) ∧
    (∀ v, 4 ≤ graph.degree v) ∧
    graph.edgeFinset.card = 60 ∧
    number graph = 3 ∧ ¬ CycleCritical graph :=
  ⟨DoublePetersenGraph.cycle_critical,DoublePetersenGraph.number_eq_five,
    even,degree_lower,edge_card,number_three,not_critical⟩

#print axioms obstruction
#print axioms quotient_hom
#print axioms quotient_edge_surjective
#print axioms identified_degree_two
end Erdos184Work.PetersenIdentification
