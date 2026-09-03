import Submission.EdgeVertexFilterMarginal
import Submission.InfiniteTriangleRamsey

/-!
The endpoint completeness of the canonical avoiding filter does not, by
itself, upgrade the completeness of that edge filter. The example here is a
large COMPLETE graph and therefore contains K4. This is an obstruction to an
abstract filter argument, not a proof or disproof of Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595CanonicalEdgeCompleteness
open Erdos595Work Erdos595CountableBadEdge Erdos595EdgeVertexMarginal

abbrev Bits := ℕ → Fin 2
abbrev Vertex := Set Bits
abbrev G : SimpleGraph Vertex := ⊤
abbrev Edge := Erdos595ArcAdjoint.Arc G
abbrev F : Filter Edge := coveringFilter G

lemma bits_card : Cardinal.mk Bits = Cardinal.continuum := by
  simp only [Bits, Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
    Cardinal.lift_uzero, Nat.cast_ofNat, Cardinal.two_power_aleph0]

/-- Properness is supplied by the already proved complete-graph Ramsey bound. -/
theorem proper : F.NeBot :=
  (coveringFilter_neBot_iff G).mpr
    Erdos595InfiniteTriangleRamsey.large_complete_no_cover

instance : F.NeBot := proper

/-- Both endpoint marginals have the stronger completeness. -/
theorem fst_complete :
    CardinalInterFilter (Filter.map (fun e : Edge => e.val.1) F)
      (Order.succ Cardinal.continuum) :=
  endpoint_cardinalInter G

theorem snd_complete :
    CardinalInterFilter (Filter.map (fun e : Edge => e.val.2) F)
      (Order.succ Cardinal.continuum) := by
  rw [← marginals_equal G F (coveringFilter_avoids G)]
  exact fst_complete

/-- Each single coordinate cut is eventually avoided. -/
lemma coordinate_agreement (b : Bits) :
    ∀ᶠ e : Edge in F, (b ∈ e.val.1 ↔ b ∈ e.val.2) :=
  endpoint_agreement G F (coveringFilter_avoids G) {S | b ∈ S}

/-- But agreement at ALL continuum many coordinates would make the endpoints
identical, contradicting the fact that the filter lives on graph edges. -/
theorem not_complete : ¬CardinalInterFilter F (Order.succ Cardinal.continuum) := by
  intro hc
  letI := hc
  have hb : Cardinal.mk Bits < Order.succ Cardinal.continuum := by
    rw [bits_card]
    exact Order.lt_succ _
  have h : ∀ᶠ e : Edge in F, ∀ b : Bits, (b ∈ e.val.1 ↔ b ∈ e.val.2) :=
    (Filter.eventually_cardinal_forall hb).mpr coordinate_agreement
  obtain ⟨e,he⟩ := h.exists
  exact e.property (Set.ext he)

/-- The failed upgrade is already false for the canonical graph filters,
not merely for an unrelated example of a joint filter. -/
theorem canonical_counterexample :
    ∃ (V : Type) (K : SimpleGraph V),
      (coveringFilter K).NeBot ∧
      CountableInterFilter (coveringFilter K) ∧
      CardinalInterFilter
        (Filter.map (fun e : Erdos595ArcAdjoint.Arc K => e.val.1) (coveringFilter K))
        (Order.succ Cardinal.continuum) ∧
      CardinalInterFilter
        (Filter.map (fun e : Erdos595ArcAdjoint.Arc K => e.val.2) (coveringFilter K))
        (Order.succ Cardinal.continuum) ∧
      ¬CardinalInterFilter (coveringFilter K) (Order.succ Cardinal.continuum) :=
  ⟨Vertex,G,proper,inferInstance,fst_complete,snd_complete,not_complete⟩

open Erdos595TriangleFilterCoupling

/-- The canonical triangle coupling is proper as well. -/
theorem triangle_proper : (triangleFilter G).NeBot :=
  (triangleFilter_neBot_iff G).mpr
    Erdos595InfiniteTriangleRamsey.large_complete_no_cover

/-- All three vertex marginals have the stronger completeness, even though
all three edge marginals are the less-complete canonical edge filter. -/
theorem triangle_vertices_complete (i : Fin 3) :
    CardinalInterFilter (Filter.map (vertex G i) (triangleFilter G))
      (Order.succ Cardinal.continuum) :=
  triangle_vertex_cardinalInter G i

theorem triangle_not_complete :
    ¬CardinalInterFilter (triangleFilter G) (Order.succ Cardinal.continuum) := by
  intro hc
  letI := hc
  apply not_complete
  change CardinalInterFilter (coveringFilter G) (Order.succ Cardinal.continuum)
  rw [← map_side G 0]
  infer_instance

#print axioms triangle_proper
#print axioms triangle_vertices_complete
#print axioms triangle_not_complete


private def four : Fin 4 ↪ Vertex where
  toFun i := {b | b i.val = 1}
  inj' := by
    intro i j he
    apply Fin.ext
    by_contra hij
    let b : Bits := fun n => if n = i.val then 1 else 0
    have h := Set.ext_iff.mp he b
    have hn : j.val ≠ i.val := Ne.symm hij
    simp only [Set.mem_setOf_eq, b, if_neg hn] at h
    exact (by decide : (0 : Fin 2) ≠ 1) (h.mp rfl)

/-- Explicitly record why this counterexample does not settle Erdos 595. -/
theorem not_cliqueFree : ¬G.CliqueFree 4 := by
  let e : (⊤ : SimpleGraph (Fin 4)) ↪g G :=
    { toFun := four
      inj' := four.injective
      map_rel_iff' := by
        intro i j
        exact ⟨fun h hij => h (congrArg four hij), fun h hij => h (four.injective hij)⟩ }
  exact SimpleGraph.not_cliqueFree_of_top_embedding e

#print axioms canonical_counterexample
#print axioms not_cliqueFree
end Erdos595CanonicalEdgeCompleteness
