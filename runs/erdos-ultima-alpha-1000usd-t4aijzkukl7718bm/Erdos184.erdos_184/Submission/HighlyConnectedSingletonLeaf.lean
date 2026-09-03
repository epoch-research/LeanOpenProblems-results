import Submission.NonCutSingletonLeaf
import Submission.HighlyConnectedVertexLoss

/-! In the sufficiently vertex-connected class, global minimality guarantees
an actual singleton-forest leaf whose deletion leaves the graph connected.
This does not establish a bounded decomposition-number loss at that leaf. -/

open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.HighlyConnectedSingletonLeaf
open Critical EdgeHull SingletonExchange VertexSeparators
set_option maxHeartbeats 1200000
universe u
variable {V : Type u} [Fintype V]

lemma forest_has_leaf {F : SimpleGraph V} (ha : F.IsAcyclic) (hne : F ≠ ⊥) :
    ∃ v : V, Nat.card (F.neighborSet v) = 1 := by
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  let c := F.connectedComponentMk a
  have haC : a ∈ c := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hbC : b ∈ c := (c.mem_supp_congr_adj hab).mp haC
  letI : Fintype c := Fintype.ofFinite _
  letI : Nontrivial c := ⟨⟨⟨a,haC⟩, ⟨b,hbC⟩, by
    intro h
    exact hab.ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨v, hv⟩ := (ha.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
  let f : c.toSimpleGraph.neighborSet v → F.neighborSet v.val :=
    fun w => ⟨w.val.val, w.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : F.neighborSet v.val => w.val) h
    · intro w
      have hw : w.val ∈ c := (c.mem_supp_congr_adj w.property).mp v.property
      exact ⟨⟨⟨w.val,hw⟩, w.property⟩, rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hv
  exact ⟨v.val, hc.symm.trans hv⟩

lemma optimal_ne_bot {G F : SimpleGraph V} (hm : Minimal G)
    (hne : G ≠ ⊥) (hf : Optimal G F) : F ≠ ⊥ := by
  intro h
  apply hne
  apply hm.edgeCritical.eq_bot_of_even
  have he := hf.2.1
  rw [h, sdiff_bot] at he
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using he

lemma connected_after_singleton [Nontrivial V] {G : SimpleGraph V}
    (hc : DeletionConnected G 1) (v : V) :
    (G.induce ({v}ᶜ : Set V)).Connected := by
  have hp := hc ({v} : Set V) (by simp)
  obtain ⟨w, hw⟩ := exists_ne v
  haveI : Nonempty ({v}ᶜ : Set V) := ⟨⟨w, by simpa using hw⟩⟩
  exact ⟨hp⟩

lemma exists_noncut_optimal_leaf [Nontrivial V] {G F : SimpleGraph V}
    (hm : Minimal G) (hne : G ≠ ⊥) (hc : DeletionConnected G 1)
    (hf : Optimal G F) :
    ∃ v : V, (G.induce ({v}ᶜ : Set V)).Connected ∧
      Nat.card (F.neighborSet v) = 1 ∧ Odd (Nat.card (G.neighborSet v)) := by
  obtain ⟨v, hv⟩ := forest_has_leaf hf.acyclic (optimal_ne_bot hm hne hf)
  refine ⟨v, connected_after_singleton hc v, hv, ?_⟩
  have hd := degree_sdiff_add G F hf.1 v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hd
  have he := Nat.even_iff.mp (hf.2.1 v)
  rw [Nat.odd_iff]
  omega

/-- A sufficient local hypothesis. This property is NOT proved here. It asks
only for one favorable Best forest and one of its actual leaves. -/
def Property (C : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
    Minimal G → DeletionConnected G 1 → 3 < Fintype.card V →
      ∃ F : SimpleGraph V, Best G F ∧ ∃ v : V,
        Nat.card (F.neighborSet v) = 1 ∧
        number G ≤ value (G.induce ({v}ᶜ : Set V)) + C

lemma asymptotic_of_property (C : ℕ) (h : Property.{u} C) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply HighlyConnectedVertexLoss.asymptotic_of_property 1 C
  intro W _ G hm hc hn
  obtain ⟨F, hf, v, hv, hb⟩ := h W G hm hc (by omega)
  exact ⟨v, hb⟩

/-- In particular, a bound valid at every leaf of every Best forest would
suffice. The quantified inequality is a hypothesis, not an established fact. -/
lemma asymptotic_of_all_leaf_bound (C : ℕ)
    (h : ∀ (W : Type u) [Fintype W] (G F : SimpleGraph W),
      Minimal G → DeletionConnected G 1 → 3 < Fintype.card W → Best G F →
        ∀ v, Nat.card (F.neighborSet v) = 1 →
          number G ≤ value (G.induce ({v}ᶜ : Set W)) + C) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply HighlyConnectedVertexLoss.asymptotic_of_property 1 C
  intro W _ G hm hc hn
  by_cases hz : G = ⊥
  · haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v⟩ := ‹Nonempty W›
    refine ⟨v, ?_⟩
    rw [hz, number_bot]
    exact Nat.zero_le _
  · obtain ⟨F, hf⟩ := exists_best G
    obtain ⟨v, hv⟩ := forest_has_leaf hf.1.acyclic (optimal_ne_bot hm hz hf.1)
    exact ⟨v, h W G F hm hc (by omega) hf v hv⟩

end Erdos184Work.HighlyConnectedSingletonLeaf

#print axioms Erdos184Work.HighlyConnectedSingletonLeaf.forest_has_leaf
#print axioms Erdos184Work.HighlyConnectedSingletonLeaf.exists_noncut_optimal_leaf
#print axioms Erdos184Work.HighlyConnectedSingletonLeaf.asymptotic_of_all_leaf_bound
