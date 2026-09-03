import Submission.FiveStatePower
import Submission.FiniteFolkman
import Submission.CountableBadEdgeFilter

/-!
The five-state family separates the finite-palette and countable-palette
questions even on one fixed graph. This is not a settlement of Erdős 595.
Every infinite coordinate set gives all finite Folkman obstructions, while
countably many coordinates give a countable bipartite edge cover.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595FiveStatePaletteBoundary
open Erdos595FiveStatePower Erdos595FinitePalette Erdos595Work

variable {I J : Type*}

noncomputable def extendPoint (e : I ↪ J) (f : I → Fin 5) : J → Fin 5 :=
  Function.extend e f (fun _ => 3)

lemma extendPoint_apply (e : I ↪ J) (f : I → Fin 5) (i : I) :
    extendPoint e f (e i) = f i := e.injective.extend_apply _ _ _

lemma extendPoint_outside (e : I ↪ J) (f : I → Fin 5) (j : J)
    (hj : j ∉ Set.range e) : extendPoint e f j = 3 := by
  classical
  exact Function.extend_apply' f (fun _ => 3) j hj

lemma extendPoint_adj_iff (e : I ↪ J) (f g : I → Fin 5) :
    (graph J).Adj (extendPoint e f) (extendPoint e g) ↔ (graph I).Adj f g := by
  classical
  constructor
  · rintro ⟨ha,j,hj⟩
    refine ⟨fun i => ?_,?_⟩
    · simpa only [extendPoint_apply] using ha (e i)
    · by_cases hr : j ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hr
        exact ⟨i,by simpa only [extendPoint_apply] using hj⟩
      · rw [extendPoint_outside e f j hr,extendPoint_outside e g j hr] at hj
        simp [Tight] at hj
  · rintro ⟨ha,i,hi⟩
    refine ⟨?_,e i,by simpa only [extendPoint_apply] using hi⟩
    intro j
    by_cases hr : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hr
      simpa only [extendPoint_apply] using ha i
    · rw [extendPoint_outside e f j hr,extendPoint_outside e g j hr]
      decide

noncomputable def coordinateEmbedding (e : I ↪ J) : graph I ↪g graph J where
  toFun := extendPoint e
  inj' := by
    intro f g h
    funext i
    have hi := congrFun h (e i)
    simpa only [extendPoint_apply] using hi
  map_rel_iff' := extendPoint_adj_iff e _ _

/-- For any infinite coordinate set, each finite palette already fails on
some finite induced subgraph of the full five-state graph. -/
theorem no_finite_palette (I : Type*) [Infinite I] (C : Type) [Finite C] :
    ¬HasColoring (graph I) C := by
  classical
  obtain ⟨V,hV,G,hG,hn⟩ := Erdos595FiniteFolkman.finite_folkman C
  letI := hV
  obtain ⟨enc,henc⟩ := exists_injective_nat (Index V)
  let e : Index V ↪ I := (⟨enc,henc⟩ : Index V ↪ ℕ).trans (Infinite.natEmbedding I)
  let f : G →g graph I := (coordinateEmbedding e).toHom.comp (embedding G hG).toHom
  exact fun hc => hn (hc.comap f)

noncomputable def coordinatePiece (I : Type*) (i : I) : SimpleGraph (I → Fin 5) := by
  classical
  exact graph I ⊓ (⊤ : SimpleGraph Bool).comap (fun f => decide (f i = 0))

lemma coordinatePiece_triangleFree (I : Type*) (i : I) :
    (coordinatePiece I i).CliqueFree 3 := by
  classical
  let c : (coordinatePiece I i).Coloring Bool :=
    SimpleGraph.Coloring.mk (fun f => decide (f i = 0)) (fun h => h.2)
  exact c.colorable.cliqueFree (by decide)

/-- No cardinal bound on the vertex type is used: the coordinates, rather
than the vertices, index the bipartite pieces. -/
theorem countable_coordinate_cover (I : Type*) [Countable I] :
    IsCountableUnionOfTriangleFree (graph I) := by
  classical
  apply Erdos595CountableBadEdge.cover_of_countable_family (graph I)
    (coordinatePiece I) (coordinatePiece_triangleFree I)
  intro f g hfg
  obtain ⟨i,hi | hi⟩ := hfg.2
  · refine ⟨i,hfg,?_⟩
    simp only [SimpleGraph.comap_adj,SimpleGraph.top_adj]
    simp [hi.1,hi.2]
  · refine ⟨i,hfg,?_⟩
    simp only [SimpleGraph.comap_adj,SimpleGraph.top_adj]
    simp [hi.1,hi.2]

/-- One fixed K4-free graph is countably covered but defeats every finite
palette. Thus the finite obstructions alone cannot settle the conjecture. -/
theorem fixed_palette_boundary :
    (graph ℕ).CliqueFree 4 ∧ IsCountableUnionOfTriangleFree (graph ℕ) ∧
      ∀ n : ℕ, ¬HasColoring (graph ℕ) (Fin n) :=
  ⟨cliqueFree ℕ,countable_coordinate_cover ℕ,fun n => no_finite_palette ℕ (Fin n)⟩

#print axioms coordinateEmbedding
#print axioms no_finite_palette
#print axioms countable_coordinate_cover
#print axioms fixed_palette_boundary
end Erdos595FiveStatePaletteBoundary
