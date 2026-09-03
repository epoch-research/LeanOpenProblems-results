import Submission.OneSidedUltrafilterObstruction
import Submission.BadEdgeUltrafilter

/-!
The order-oriented Fubini extension. It retains the forward direction in a
chosen linear order, not the conjunction of the two directions. This is a
construction and a set of obstructions, not a settlement of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595OrderedUltrafilter
open Erdos595Work Erdos595OneSided

variable {V I : Type*} [LinearOrder (Ultrafilter V)]

def graph (G : SimpleGraph V) : SimpleGraph (Ultrafilter V) :=
  forwardGraph (fubiniAdj G)

lemma adj_of_lt (G : SimpleGraph V) {p q : Ultrafilter V} (h : p < q) :
    (graph G).Adj p q ↔ fubiniAdj G p q := by
  exact ⟨fun h' => h'.elim And.right (fun h' => (lt_asymm h h'.1).elim),
    fun h' => Or.inl ⟨h,h'⟩⟩

/-- All six edges of an ordered four-clique have the correct Fubini direction
for the existing four-point extraction argument. -/
theorem cliqueFree_four (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (graph G).CliqueFree 4 := by
  classical
  intro t ht
  let e : Fin 4 ↪o Ultrafilter V := t.orderEmbOfFin ht.card_eq
  have hm : ∀ i, e i ∈ (t : Set (Ultrafilter V)) :=
    fun i => t.orderEmbOfFin_mem ht.card_eq i
  have he : ∀ i j : Fin 4, i < j → fubiniAdj G (e i) (e j) := by
    intro i j hij
    apply (adj_of_lt G (e.strictMono hij)).mp
    exact ht.isClique (hm i) (hm j) (fun h => hij.ne (e.injective h))
  exact no_four_fubini G hG (e 0) (e 1) (e 2) (e 3)
    (he 0 1 (by decide)) (he 0 2 (by decide)) (he 0 3 (by decide))
    (he 1 2 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

theorem cliqueFree_three (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (graph G).CliqueFree 3 :=
  forwardGraph_cliqueFree (fubiniAdj G) (Erdos595OneSided.no_three_fubini G hG)

/-- The mutual extension is a subgraph of every order-oriented extension. -/
theorem mutual_le (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    ultrafilterGraph G hG ≤ graph G := by
  intro p q hpq
  rcases lt_or_gt_of_ne hpq.ne with h | h
  · exact Or.inl ⟨h,hpq.1⟩
  · exact Or.inr ⟨h,hpq.2⟩

/-- Neighborhood traces still separate edges even though only one Fubini
direction is retained. -/
theorem trace_coloring (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    Nonempty ((graph G).Coloring (Set V)) := by
  refine ⟨SimpleGraph.Coloring.mk (fun p => {v | G.neighborSet v ∈ p}) ?_⟩
  intro p q hpq he
  dsimp only at he
  rcases hpq with ⟨_,hpq⟩ | ⟨_,hqp⟩
  · have hpp : fubiniAdj G p p := by
      change {v | G.neighborSet v ∈ p} ∈ p
      rw [he]
      exact hpq
    exact no_four_fubini G hG p p p p hpp hpp hpp hpp hpp hpp
  · have hqq : fubiniAdj G q q := by
      change {v | G.neighborSet v ∈ q} ∈ q
      rw [← he]
      exact hqp
    exact no_four_fubini G hG q q q q hqq hqq hqq hqq hqq hqq

/-- One extension of a countable base cannot give a witness, regardless of
the chosen linear order. -/
theorem countable_base [Countable V] (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    IsCountableUnionOfTriangleFree (graph G) := by
  classical
  let f : V ↪ ℕ := ⟨(exists_injective_nat V).choose, (exists_injective_nat V).choose_spec⟩
  let enc : Set V → ℕ → Fin 2 := fun S n => if ∃ v ∈ S, f v = n then 1 else 0
  have hi : Function.Injective enc := by
    intro S T h
    ext v
    have he := congrFun h (f v)
    have hS : (∃ w ∈ S, f w = f v) ↔ v ∈ S := by
      constructor
      · rintro ⟨w,hw,he⟩; exact f.injective he ▸ hw
      · exact fun hv => ⟨v,hv,rfl⟩
    have hT : (∃ w ∈ T, f w = f v) ↔ v ∈ T := by
      constructor
      · rintro ⟨w,hw,he⟩; exact f.injective he ▸ hw
      · exact fun hv => ⟨v,hv,rfl⟩
    simp only [enc,hS,hT] at he
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all
  exact countable_union_of_coloring _
    ((graph G).recolorOfEmbedding ⟨enc,hi⟩ (trace_coloring G hG).some)

/-- Finite suprema commute with this extension exactly. This is not true for
countably infinite suprema by the same argument. -/
theorem finite_iSup [Finite I] (H : I → SimpleGraph V) :
    graph (⨆ i, H i) = ⨆ i, graph (H i) := by
  ext p q
  simp only [SimpleGraph.iSup_adj, graph, forwardGraph, fubiniAdj_finite_iSup]
  constructor
  · rintro (⟨h, i, hi⟩ | ⟨h,i,hi⟩)
    · exact ⟨i,Or.inl ⟨h,hi⟩⟩
    · exact ⟨i,Or.inr ⟨h,hi⟩⟩
  · rintro ⟨i, (⟨h,hi⟩ | ⟨h,hi⟩)⟩
    · exact Or.inl ⟨h,i,hi⟩
    · exact Or.inr ⟨h,i,hi⟩

/-- A finite triangle-free cover is preserved, with the same number of pieces. -/
theorem finite_cover (G : SimpleGraph V) (hG : Erdos595BadEdge.FiniteCover G) :
    Erdos595BadEdge.FiniteCover (graph G) := by
  classical
  obtain ⟨n,H,hH,hcov⟩ := hG
  let K : Fin n → SimpleGraph V := fun i => G ⊓ H i
  have hk : ∀ i, (K i).CliqueFree 3 := fun i => (hH i).anti inf_le_right
  have he : G = ⨆ i, K i := by
    ext a b
    simp only [SimpleGraph.iSup_adj, K, SimpleGraph.inf_adj]
    exact ⟨fun hab => let ⟨i,hi⟩ := hcov a b hab; ⟨i,hab,hi⟩,
      fun ⟨_,hab,_⟩ => hab⟩
  refine ⟨n,fun i => graph (K i),fun i => cliqueFree_three (K i) (hk i),?_⟩
  intro p q hpq
  rw [he,finite_iSup,SimpleGraph.iSup_adj] at hpq
  exact hpq

lemma fubini_pure (G : SimpleGraph V) (v w : V) :
    fubiniAdj G (pure v) (pure w) ↔ G.Adj v w := by
  simp only [fubiniAdj, Ultrafilter.mem_pure, Set.mem_setOf_eq,
    SimpleGraph.mem_neighborSet]

/-- The original graph is an induced subgraph, in every choice of extension order. -/
noncomputable def pureEmbedding (G : SimpleGraph V) : G ↪g graph G where
  toFun := pure
  inj' := Ultrafilter.pure_injective
  map_rel_iff' := by
    intro v w
    constructor
    · rintro (⟨_,h⟩ | ⟨_,h⟩)
      · exact (fubini_pure G v w).mp h
      · exact ((fubini_pure G w v).mp h).symm
    · intro h
      have hn : (pure v : Ultrafilter V) ≠ pure w :=
        fun he => h.ne (Ultrafilter.pure_injective he)
      rcases lt_or_gt_of_ne hn with ho | ho
      · exact Or.inl ⟨ho,(fubini_pure G v w).mpr h⟩
      · exact Or.inr ⟨ho,(fubini_pure G w v).mpr h.symm⟩

#print axioms finite_cover
#print axioms pureEmbedding
#print axioms cliqueFree_four
#print axioms countable_base
#print axioms finite_iSup
end Erdos595OrderedUltrafilter
