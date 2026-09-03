import Submission.ThreeHubMinimalLeaves

/-! Structural restrictions on globally minimal subgraphs of a three-hub
complete bipartite graph. These do not settle the original conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ThreeHubFullStructure
open Critical EdgeHull ThreeHubMinimalLeaves
set_option maxHeartbeats 1200000
variable {B : Type*} [Fintype B] {G : SimpleGraph (Fin 3 ⊕ B)}

/-- A right-side vertex is full when it is adjacent to all three hubs. -/
def Full (G : SimpleGraph (Fin 3 ⊕ B)) (b : B) : Prop :=
  ∀ a : Fin 3, G.Adj (.inr b) (.inl a)

lemma full_degree (hG : G ≤ completeBipartiteGraph (Fin 3) B)
    {b : B} (hb : Full G b) : G.degree (.inr b) = 3 := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  rw [degree_right hG]
  have he : {a : Fin 3 // G.Adj (.inr b) (.inl a)} = {a : Fin 3 // True} := by
    congr 1
    funext a
    exact propext ⟨fun _ => trivial, fun _ => hb a⟩
  rw [he]
  simp

lemma degree_eq_three_iff_full (hG : G ≤ completeBipartiteGraph (Fin 3) B)
    (b : B) : G.degree (.inr b) = 3 ↔ Full G b := by
  refine ⟨?_, full_degree hG⟩
  intro hd a
  have hc : Nat.card {a : Fin 3 // G.Adj (.inr b) (.inl a)} = 3 := by
    rw [← degree_right hG]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hd
  by_contra hn
  have hlt : Fintype.card {a : Fin 3 // G.Adj (.inr b) (.inl a)} <
      Fintype.card (Fin 3) := Fintype.card_subtype_lt hn
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at hlt
  omega

/-- A full right-side vertex supplies a square through every degree-two
right-side vertex. Such a square is impossible in a globally minimal graph. -/
lemma no_degree_two_of_full (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) {b₀ : B} (hfull : Full G b₀)
    (b : B) : G.degree (.inr b) ≠ 2 := by
  intro hd
  have hb : b ≠ b₀ := by
    intro h
    subst b
    have h := full_degree hG hfull
    omega
  have hc : {a : Fin 3 | G.Adj (.inr b) (.inl a)}.ncard = 2 := by
    change Nat.card {a : Fin 3 // G.Adj (.inr b) (.inl a)} = 2
    rw [← degree_right hG]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hd
  obtain ⟨a,c,hac,hs⟩ := Set.ncard_eq_two.mp hc
  have ha : G.Adj (.inr b) (.inl a) := by
    change a ∈ {a : Fin 3 | G.Adj (.inr b) (.inl a)}
    rw [hs]
    simp
  have hc' : G.Adj (.inr b) (.inl c) := by
    change c ∈ {a : Fin 3 | G.Adj (.inr b) (.inl a)}
    rw [hs]
    simp
  let p : G.Walk (.inr b) (.inr b) :=
    .cons ha (.cons (hfull a).symm (.cons (hfull c) (.cons hc'.symm .nil)))
  have hp : p.IsCycle := by
    simp [p, Walk.isCycle_def, Walk.isTrail_def, hb, Ne.symm hb, hac, Ne.symm hac,
      Sym2.eq_iff]
  have hdeg := hm.cycle_vertex_degree hp p.start_mem_support
  omega

lemma nonfull_degree_le_one (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) {b₀ : B} (hfull : Full G b₀)
    {b : B} (hb : ¬ Full G b) : G.degree (.inr b) ≤ 1 := by
  have hne := no_degree_two_of_full hm hG hfull b
  have hn3 := mt (degree_eq_three_iff_full hG b).mp hb
  have hu := SimpleGraph.degree_le_of_le (v := .inr b) hG
  have hh := degree_right_full (A := Fin 3) b
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_fin] at hne hn3 hu hh ⊢
  omega

end Erdos184Work.ThreeHubFullStructure
#print axioms Erdos184Work.ThreeHubFullStructure.no_degree_two_of_full
#print axioms Erdos184Work.ThreeHubFullStructure.nonfull_degree_le_one
