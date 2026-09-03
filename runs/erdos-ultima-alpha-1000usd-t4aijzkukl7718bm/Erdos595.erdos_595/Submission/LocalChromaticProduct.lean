import Submission.CompleteFilterProduct

/-!
Finite chromatic numbers in coordinate neighborhoods remain finite in
proper countably complete reduced products. The resulting graph therefore
has a countable triangle-free edge cover. The bounds need not be uniform,
and no clique bound is needed. This does not settle Erdős 595.
-/

open SimpleGraph Set Filter
namespace Erdos595LocalChromaticProduct
open Erdos595CompleteFilterProduct

variable {V : Type*}

/-- Local proper colorings may be reused at the larger endpoint of each edge. -/
theorem cover_of_neighborhood_colorings (G : SimpleGraph V)
    (hG : ∀ v, Nonempty ((G.induce (G.neighborSet v)).Coloring ℕ)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  let c (v : V) : (G.induce (G.neighborSet v)).Coloring ℕ := (hG v).some
  let f (v w : V) := if h : G.Adj v w then c v ⟨w,h⟩ else 0
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595Work.countable_union_of_earlier_neighbor_coloring G f
  intro a b d _ _ hab had hbd
  simpa only [f,dif_pos hab,dif_pos had] using
    (c a).valid (show (G.induce (G.neighborSet a)).Adj ⟨b,hab⟩ ⟨d,had⟩ from hbd)

/-- The induced neighborhood, considered as a spanning graph with isolated
vertices outside the neighborhood. This avoids nonemptiness requirements
on coordinate neighborhoods. -/
def localPiece (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj v a ∧ G.Adj v b
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1.ne rfl

lemma localPiece_colorable (G : SimpleGraph V) (v : V) {n : ℕ}
    (h : (G.induce (G.neighborSet v)).Colorable n) :
    (localPiece G v).Colorable (n + 1) := by
  classical
  obtain ⟨c⟩ := h
  let f : V → Fin (n + 1) := fun a =>
    if ha : G.Adj v a then (c ⟨a,ha⟩).castSucc else Fin.last n
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro a b hab he
  have hh : (c ⟨a,hab.2.1⟩).castSucc = (c ⟨b,hab.2.2⟩).castSucc := by
    simpa only [f,dif_pos hab.2.1,dif_pos hab.2.2] using he
  exact c.valid (show (G.induce (G.neighborSet v)).Adj
    ⟨a,hab.2.1⟩ ⟨b,hab.2.2⟩ from hab.1) (Fin.castSucc_injective n hh)

variable {I : Type*} {A : I → Type*}

/-- A product neighborhood maps into the product of spanning coordinate
neighborhoods. Adjacency to the anchor need only hold eventually. -/
def neighborhoodHom (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i)) (x : ∀ i, A i) :
    (graph F G).induce ((graph F G).neighborSet x) →g
      graph F (fun i => localPiece (G i) (x i)) where
  toFun := Subtype.val
  map_rel' := by
    intro y z hyz
    exact hyz.and (y.property.and z.property)

/-- Even the finite bound may depend on the product vertex. -/
theorem neighborhoods_finitely_colorable (F : Filter I) [F.NeBot]
    [CountableInterFilter F] (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i v, ∃ n, ((G i).induce ((G i).neighborSet v)).Colorable n)
    (x : ∀ i, A i) :
    ∃ n, ((graph F G).induce ((graph F G).neighborSet x)).Colorable n := by
  have hp : ∀ i, ∃ n, (localPiece (G i) (x i)).Colorable n := by
    intro i
    obtain ⟨n,hn⟩ := hG i (x i)
    exact ⟨n + 1,localPiece_colorable (G i) (x i) hn⟩
  obtain ⟨n,⟨c⟩⟩ := finitely_colorable F (fun i => localPiece (G i) (x i)) hp
  exact ⟨n,⟨c.comp (neighborhoodHom F G x)⟩⟩

/-- Locally finite chromatic coordinate graphs cannot produce a witness.
This is stronger than requiring finite global coordinate palettes. -/
theorem countable_cover (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i v, ∃ n, ((G i).induce ((G i).neighborSet v)).Colorable n) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph F G) := by
  apply cover_of_neighborhood_colorings
  intro x
  obtain ⟨n,⟨c⟩⟩ := neighborhoods_finitely_colorable F G hG x
  exact ⟨SimpleGraph.Coloring.mk (fun y => (c y).val)
    (fun h he => c.valid h (Fin.ext he))⟩

/-- In particular, arbitrary locally finite factors are ruled out, even
when they have infinite vertex sets and unbounded finite chromatic numbers. -/
theorem locally_finite_cover (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) [∀ i, (G i).LocallyFinite] :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph F G) := by
  apply countable_cover F G
  intro i v
  exact ⟨Fintype.card ((G i).neighborSet v),SimpleGraph.colorable_of_fintype _⟩

#print axioms cover_of_neighborhood_colorings
#print axioms neighborhoods_finitely_colorable
#print axioms countable_cover
#print axioms locally_finite_cover
end Erdos595LocalChromaticProduct
