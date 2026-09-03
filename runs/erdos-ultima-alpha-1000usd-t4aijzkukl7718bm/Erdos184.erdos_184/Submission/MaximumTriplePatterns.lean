import Submission.DoubleTripleContacts
import Submission.CycleContactLower

/-! Numerical contact patterns forced in small subfamilies of a
maximum cycle partition. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MaximumCoreFamilies
open Critical MaximumCycles CycleContactLower
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def AdmissibleTriple (a b c : ℕ) : Prop :=
  a ≤ 2 ∧ b ≤ 2 ∧ c ≤ 2 ∧ 2 ≤ a+b ∧ 2 ≤ a+c ∧ 2 ≤ b+c ∧ ¬ (a=2 ∧ b=2 ∧ c=2)

lemma admissible_triple_cases (a b c : ℕ) : AdmissibleTriple a b c ↔
    ((1 ≤ a ∧ a ≤ 2) ∧ (1 ≤ b ∧ b ≤ 2) ∧ (1 ≤ c ∧ c ≤ 2) ∧ (a=1 ∨ b=1 ∨ c=1)) ∨
      (a=0 ∧ b=2 ∧ c=2) ∨ (a=2 ∧ b=0 ∧ c=2) ∨ (a=2 ∧ b=2 ∧ c=0) := by
  unfold AdmissibleTriple
  omega

lemma three_piece_contacts_sum (H K L : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hL : L.coe.Connected ∧ L.coe.IsRegularOfDegree 2)
    (hHK : H ≠ K) (hHL : H ≠ L) (hKL : K ≠ L)
    (hd : Set.PairwiseDisjoint ({H,K,L} : Set G.Subgraph) (fun M => M.edgeSet))
    (hn : number (subfamilyGraph {H,K,L}) ≤ 2) :
    2 ≤ (H.verts ∩ K.verts).ncard + (H.verts ∩ L.verts).ncard := by
  have hprop : ∀ M ∈ ({H,K,L} : Finset G.Subgraph), M.coe.Connected ∧ M.coe.IsRegularOfDegree 2 := by
    intro M hM
    simp only [Finset.mem_insert,Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl
    · exact hH
    · exact hK
    · exact hL
  have hpd : Set.PairwiseDisjoint (({H,K,L} : Finset G.Subgraph) : Set G.Subgraph) (fun M => M.edgeSet) := by
    simpa using hd
  have hb := two_contacts_of_number_le_two {H,K,L} hprop hpd
    (by simp [hHK,hHL,hKL]) hn H (by simp)
  have herase : ({H,K,L} : Finset G.Subgraph).erase H = {K,L} := by simp [hHK,hHL]
  rw [herase] at hb
  have hv : vertexUnion ({K,L} : Finset G.Subgraph) = K.verts ∪ L.verts := by
    simp only [vertexUnion,Finset.set_biUnion_insert,Finset.set_biUnion_singleton]
  rw [hv,Set.inter_union_distrib_left] at hb
  exact hb.trans (Set.ncard_union_le _ _)

lemma maximum_triple_admissible {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (T : Fin 3 → G.Subgraph) (hT : Function.Injective T) (hmem : ∀ i, T i ∈ D)
    (hn : number (subfamilyGraph {T 0,T 1,T 2}) ≤ 2) :
    AdmissibleTriple ((T 0).verts ∩ (T 1).verts).ncard
      ((T 0).verts ∩ (T 2).verts).ncard ((T 1).verts ∩ (T 2).verts).ncard := by
  have hne (i j : Fin 3) (hij : i ≠ j) : T i ≠ T j := fun h => hij (hT h)
  have hprop (i : Fin 3) := hD.1 (T i) (hmem i)
  have hp (i j k : Fin 3) :
      Set.PairwiseDisjoint ({T i,T j,T k} : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hHK
    have hHD : H ∈ D := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hH
      rcases hH with rfl | rfl | rfl <;> exact hmem _
    have hKD : K ∈ D := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl | rfl <;> exact hmem _
    exact hD.2.1.1 hHD hKD hHK
  have hbound (i j : Fin 3) (hij : i ≠ j) : ((T i).verts ∩ (T j).verts).ncard ≤ 2 :=
    maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 _ _ (hmem i) (hmem j) (hne i j hij)
  have h0 := three_piece_contacts_sum (T 0) (T 1) (T 2) (hprop 0) (hprop 1) (hprop 2)
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide)) (hp 0 1 2) hn
  have h1 := three_piece_contacts_sum (T 1) (T 0) (T 2) (hprop 1) (hprop 0) (hprop 2)
    (hne 1 0 (by decide)) (hne 1 2 (by decide)) (hne 0 2 (by decide)) (hp 1 0 2) (by
      have he : ({T 1,T 0,T 2} : Finset G.Subgraph) = {T 0,T 1,T 2} := by ext H; simp; tauto
      rw [he]; exact hn)
  have h2 := three_piece_contacts_sum (T 2) (T 0) (T 1) (hprop 2) (hprop 0) (hprop 1)
    (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 0 1 (by decide)) (hp 2 0 1) (by
      have he : ({T 2,T 0,T 1} : Finset G.Subgraph) = {T 0,T 1,T 2} := by ext H; simp; tauto
      rw [he]; exact hn)
  refine ⟨hbound 0 1 (by decide),hbound 0 2 (by decide),hbound 1 2 (by decide),h0,?_,?_,
    DoubleTripleCertificates.maximum_three_pieces_four_degree hD hdeg T hT hmem⟩
  · simpa only [Set.inter_comm] using h1
  · simpa only [Set.inter_comm] using h2

lemma three_core_admissible_family (he : ∀ x, Even (G.degree x))
    (hm : EvenCore.EvenMinimal G) (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G) :
    ∃ D : Finset G.Subgraph, IsMaximum G D ∧ 3 < D.card ∧
      ∀ T : Fin 3 → G.Subgraph, Function.Injective T → (∀ i, T i ∈ D) →
        AdmissibleTriple ((T 0).verts ∩ (T 1).verts).ncard
          ((T 0).verts ∩ (T 2).verts).ncard ((T 1).verts ∩ (T 2).verts).ncard := by
  obtain ⟨D,hD,hcard,_,_,hthree⟩ := three_core_maximum_family he hm hn hr
  refine ⟨D,hD,hcard,?_⟩
  intro T hT hmem
  apply maximum_triple_admissible hD (degree_le_four_of_nonrigid_three he hm hn hr) T hT hmem
  apply hthree {T 0,T 1,T 2}
  · intro H hH
    simp only [Finset.mem_insert,Finset.mem_singleton] at hH
    rcases hH with rfl | rfl | rfl <;> exact hmem _
  · have h01 : T 0 ≠ T 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hT h)
    have h02 : T 0 ≠ T 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hT h)
    have h12 : T 1 ≠ T 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hT h)
    simp [h01,h02,h12]

#print axioms three_core_admissible_family
#print axioms maximum_triple_admissible
end Erdos184Work.MaximumCoreFamilies
