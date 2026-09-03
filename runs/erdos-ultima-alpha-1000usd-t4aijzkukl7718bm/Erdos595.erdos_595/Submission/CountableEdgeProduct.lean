import Submission.CountableBadEdgeFilter
import Submission.SampledFilterProduct
import Submission.TriangleComponentProduct

/-!
Countably many edge-detecting coordinate maps preserve countable triangle-free
EDGE coverability. Consequently ANY proper filter on a countable index set
preserves the covering property. Coordinate proper vertex colorings are not
needed. This strengthens the earlier sampling/component product exclusions.
-/
set_option autoImplicit false
open Set SimpleGraph Filter
namespace Erdos595CountableEdgeProduct
open Erdos595Work Erdos595CompleteFilterProduct

variable {V I : Type*} {A : I → Type*}

/-- The maps need not be homomorphisms: every G-edge need only be detected
by at least one of the countably many coordinate graphs. -/
theorem cover_of_edge_detection [Countable I]
    (G : SimpleGraph V) (H : ∀ i, SimpleGraph (A i))
    (hH : ∀ i, IsCountableUnionOfTriangleFree (H i))
    (f : ∀ i, V → A i)
    (hdetect : ∀ x y, G.Adj x y → ∃ i, (H i).Adj (f i x) (f i y)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  choose K hK hcov using hH
  let P : I × ℕ → SimpleGraph V := fun p => (K p.1 p.2).comap (f p.1)
  apply Erdos595CountableBadEdge.cover_of_countable_family G P
  · intro p s hs
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact hK p.1 p.2 _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show (K p.1 p.2).Adj (f p.1 x) (f p.1 y) ∧
        (K p.1 p.2).Adj (f p.1 x) (f p.1 z) ∧
        (K p.1 p.2).Adj (f p.1 y) (f p.1 z) from ⟨hxy,hxz,hyz⟩))
  · intro x y hxy
    obtain ⟨i,hi⟩ := hdetect x y hxy
    rw [hcov i,SimpleGraph.iSup_adj] at hi
    obtain ⟨n,hn⟩ := hi
    exact ⟨(i,n),hn⟩

/-- The sample range need only meet every filter-large set. -/
theorem cover_of_positive_range (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, IsCountableUnionOfTriangleFree (G i))
    (s : ℕ → I) (hs : (F ⊓ Filter.principal (Set.range s)).NeBot) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  letI : (F ⊓ Filter.principal (Set.range s)).NeBot := hs
  apply cover_of_edge_detection (graph F G) (fun n => G (s n))
    (fun n => hG (s n)) (fun n x => x (s n))
  intro x y hxy
  have hAdj : ∀ᶠ i in F ⊓ Filter.principal (Set.range s), (G i).Adj (x i) (y i) :=
    (show F ⊓ Filter.principal (Set.range s) ≤ F from inf_le_left) hxy
  have hRange : ∀ᶠ i in F ⊓ Filter.principal (Set.range s), i ∈ Set.range s :=
    (show F ⊓ Filter.principal (Set.range s) ≤ Filter.principal (Set.range s)
      from inf_le_right) (Filter.mem_principal_self _)
  obtain ⟨i,hi,n,rfl⟩ := (hAdj.and hRange).exists
  exact ⟨n,hi⟩

/-- No uniform finite bound, vertex-coloring bound, or triangle-component
hypothesis is needed for ANY proper filter on a countable index set. -/
theorem countable_index_cover [Countable I] (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, IsCountableUnionOfTriangleFree (G i)) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  apply cover_of_edge_detection (graph F G) G hG (fun i x => x i)
  intro x y hxy
  exact hxy.exists

theorem cover_of_sampler (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, IsCountableUnionOfTriangleFree (G i))
    (s : ℕ → I) (hs : Tendsto s atTop F) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  apply cover_of_edge_detection (graph F G) (fun n => G (s n))
    (fun n => hG (s n)) (fun n x => x (s n))
  intro x y hxy
  exact (hs.eventually hxy).exists

theorem countably_generated_cover (F : Filter I) [F.NeBot] [F.IsCountablyGenerated]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, IsCountableUnionOfTriangleFree (G i)) :
    IsCountableUnionOfTriangleFree (graph F G) := by
  obtain ⟨s,hs⟩ := Erdos595SampledProduct.exists_sampler F
  exact cover_of_sampler F G hG s hs

/-- Representatives do not create a gap for the usual quotient versions. -/
theorem quotient_countable_index [Countable I] (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i, IsCountableUnionOfTriangleFree (G i))
    (S : Setoid (∀ i, A i)) :
    IsCountableUnionOfTriangleFree
      ((graph F G).comap (Quotient.out : Quotient S → (∀ i, A i))) :=
  countable_union_of_hom (SimpleGraph.Hom.comap _ _) (countable_index_cover F G hG)

/-- If one states the assumption componentwise, only EDGE covers are needed;
the coordinate graphs themselves are then covered by the component gluing. -/
theorem countable_index_components [Countable I] (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i))
    (hG : ∀ i q, IsCountableUnionOfTriangleFree
      (Erdos595TriangleComponentProduct.piece (G i) q)) :
    IsCountableUnionOfTriangleFree (graph F G) :=
  countable_index_cover F G (fun i =>
    Erdos595TriangleComponentProduct.cover_of_pieces (G i) (hG i))

#print axioms cover_of_edge_detection
#print axioms cover_of_positive_range
#print axioms countable_index_cover
#print axioms countably_generated_cover
#print axioms quotient_countable_index
#print axioms countable_index_components
end Erdos595CountableEdgeProduct
