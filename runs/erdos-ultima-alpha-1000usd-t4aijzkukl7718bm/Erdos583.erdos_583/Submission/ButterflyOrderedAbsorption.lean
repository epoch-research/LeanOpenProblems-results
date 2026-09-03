import Submission.ButterflyRoutes

/-! Expanding the checked two-triangle routes into arbitrary simple path intervals. -/
namespace Erdos583ButterflyOrderedAbsorptionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma mapped_core_edge_injective {N M : ℕ} {V : Type*} (s t : Fin M → Fin N)
    (he : Function.Injective (fun i ↦ s(s i,t i))) (f : Fin N → V) (hf : Function.Injective f) :
    Function.Injective (fun i ↦ s(f (s i),f (t i))) := by
  intro i j hij
  apply he
  apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp hij with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨hf h1,hf h2⟩
  · exact Or.inr ⟨hf h1,hf h2⟩

lemma base_edge_injective : Function.Injective (fun i ↦ s(baseSource i,baseTarget i)) := by decide

lemma excursion_edge_injective : Function.Injective (fun i ↦ s(Excursion.source i,Excursion.target i)) := by decide

lemma ordered_missing_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (n : Fin 3) (p : Fin (n.val+1) → Fin 4) (hp : Function.Injective p)
    (f : Fin 5 → V) (hf : Function.Injective f) (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (P : G.Walk a b) (hP : P.IsPath) (h : Fin (n.val+1) → ℕ) (hh : StrictMono h)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=f (outer (p i)))
    (hmarked : ∀ x, f x ∈ P.support → ∃ j, outer (p j)=x)
    (havoid : ∀ i, s(f (baseSource i),f (baseTarget i)) ∉ P.edges) :
    TwoPathCover (G := G) (coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨z,X,Y,hX,hY,hXY,hcov⟩ := Missing.exists_routes n p hp
  exact absorption_from_routes baseSource baseTarget (outer ∘ p) f P h hh hc ha hf hP hb hmarked
    (mapped_core_edge_injective _ _ base_edge_injective f hf) havoid X Y hX hY hXY hcov

lemma ordered_excursion_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (q : Fin 5 → Fin 6) (hq : Function.Injective q) (hn : ∀ i, q i ≠ 0)
    (h0 : q 0 ≠ 5) (h4 : q 4 ≠ 5)
    (f : Fin 6 → V) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (Excursion.source i)) (f (Excursion.target i)))
    (P : G.Walk a b) (hP : P.IsPath) (h : Fin 5 → ℕ) (hh : StrictMono h)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=f (q i))
    (hmarked : ∀ x, f x ∈ P.support → ∃ j, q j=x)
    (havoid : ∀ i, s(f (Excursion.source i),f (Excursion.target i)) ∉ P.edges) :
    TwoPathCover (G := G) (coreEdges Excursion.source Excursion.target f ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨X,Y,hX,hY,hXY,hcov⟩ := Excursion.exists_routes q hq hn h0 h4
  exact absorption_from_routes Excursion.source Excursion.target q f P h hh hc ha hf hP hb hmarked
    (mapped_core_edge_injective _ _ excursion_edge_injective f hf) havoid X Y hX hY hXY hcov

end Erdos583ButterflyOrderedAbsorptionDevelopment
