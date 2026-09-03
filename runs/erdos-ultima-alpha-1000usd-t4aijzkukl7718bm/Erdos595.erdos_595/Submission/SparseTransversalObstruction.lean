import Submission.SecondArcNormalForm
import Submission.SecondArcCover
import Submission.RightProperTransversal
import Submission.InfiniteTripleRamsey
import Submission.MiddleCornerObstruction

/-!
The sparse second-right normal form cannot universally be covered by finding
countably properly colored triangle transversals in its first right stage.
There are K4-free examples in the exact normal form with no such transversal.
This is an obstruction to that proof method, NOT a solution of Erdős 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set SimpleGraph
namespace Erdos595SparseTransversalObstruction
open Erdos595ArcAdjoint Erdos595Work Erdos595SecondArcNormalForm

variable {V W C : Type*}

def VertexTriangleRamsey (G : SimpleGraph V) (C : Type*) : Prop :=
  ∀ c : V → C, ∃ a b d, G.Adj a b ∧ G.Adj a d ∧ G.Adj b d ∧
    c a = c b ∧ c a = c d

def CountablyProperTransversal (H : SimpleGraph W) : Prop :=
  ∃ S : Set W, (H.induce Sᶜ).CliqueFree 3 ∧ Nonempty ((H.induce S).Coloring ℕ)

/-- The transversal criterion gives a vertex coloring by subsets of Nat
whose fibers contain no triangle, not just an edge cover. -/
theorem no_transversal_of_hom (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : VertexTriangleRamsey G (Set ℕ)) (f : G →g right H) :
    ¬CountablyProperTransversal H := by
  rintro ⟨S,hS,⟨c⟩⟩
  obtain ⟨a,b,d,hab,had,hbd,he₁,he₂⟩ :=
    hG (fun v => Erdos595RightProperTransversal.code H S c (f v))
  exact Erdos595RightProperTransversal.no_triangle H S hS c (f a) (f b) (f d)
    (f.map_adj hab) (f.map_adj had) (f.map_adj hbd) he₁ he₂

/-- An arbitrary-palette vertex Ramsey instance that nevertheless has a
TWO-piece edge cover: the one/two-step shift-square graph. -/
theorem shift_vertex_ramsey (C : Type) [Nonempty C] :
    ∃ (A : Type) (_ : LinearOrder A),
      (Erdos595MiddleCorner.graph A).CliqueFree 4 ∧
      IsCountableUnionOfTriangleFree (Erdos595MiddleCorner.graph A) ∧
      VertexTriangleRamsey (Erdos595MiddleCorner.graph A) C := by
  classical
  obtain ⟨A,oA,wA,hA⟩ := Erdos595InfiniteTripleRamsey.triple_ramsey_host (Fin 5) C
  letI : LinearOrder A := oA
  letI : WellFoundedLT A := wA
  refine ⟨A,oA,Erdos595MiddleCorner.graph_cliqueFree A,
    Erdos595MiddleCorner.graph_cover A,?_⟩
  intro c
  let d : A → A → A → C := fun a b t =>
    if h : a < b ∧ b < t then c ⟨a,b,t,h.1,h.2⟩ else Classical.arbitrary C
  obtain ⟨f,k,hf⟩ := hA d
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have h34 : f 3 < f 4 := f.strictMono (by decide)
  let x : Erdos595MiddleCorner.Triple A := ⟨f 0,f 1,f 2,h01,h12⟩
  let y : Erdos595MiddleCorner.Triple A := ⟨f 1,f 2,f 3,h12,h23⟩
  let z : Erdos595MiddleCorner.Triple A := ⟨f 2,f 3,f 4,h23,h34⟩
  have hx : c x = k := by
    simpa only [d,dif_pos (And.intro h01 h12)] using hf 0 1 2 (by decide) (by decide)
  have hy : c y = k := by
    simpa only [d,dif_pos (And.intro h12 h23)] using hf 1 2 3 (by decide) (by decide)
  have hz : c z = k := by
    simpa only [d,dif_pos (And.intro h23 h34)] using hf 2 3 4 (by decide) (by decide)
  exact ⟨x,y,z,Or.inl (Or.inl ⟨rfl,rfl⟩),Or.inl (Or.inr rfl),
    Or.inl (Or.inl ⟨rfl,rfl⟩),hx.trans hy.symm,hx.trans hz.symm⟩

/-- Already a two-edge-coverable source can rule out the proposed proper
transversal in the first stage of its exact two-step normal form. -/
theorem covered_source_no_transversal :
    ∃ (V : Type) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ IsCountableUnionOfTriangleFree G ∧
      (right (right (arcGraph (arcGraph G)))).CliqueFree 4 ∧
      ¬CountablyProperTransversal (right (arcGraph (arcGraph G))) := by
  obtain ⟨A,oA,hA,hcov,hRam⟩ := shift_vertex_ramsey (Set ℕ)
  letI : LinearOrder A := oA
  let G := Erdos595MiddleCorner.graph A
  refine ⟨_,G,hA,hcov,
    (Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hA,?_⟩
  exact no_transversal_of_hom G (right (arcGraph (arcGraph G))) hRam
    (Erdos595SecondArcReflection.unitTwice G)

/-- Thus the K4-free second-right hypothesis plus BOTH sparse-base properties
do NOT imply existence of a countably properly colored triangle transversal
in the first right graph. No non-coverability conclusion follows. -/
theorem sparse_no_transversal :
    ∃ (V : Type) (H : SimpleGraph V), SparseTriangleBase H ∧
      (right (right H)).CliqueFree 4 ∧ ¬CountablyProperTransversal (right H) := by
  obtain ⟨V,G,_,_,h4,hn⟩ := covered_source_no_transversal
  exact ⟨_,arcGraph (arcGraph G),second_arc_sparse G,h4,hn⟩

#print axioms no_transversal_of_hom
#print axioms shift_vertex_ramsey
#print axioms covered_source_no_transversal
#print axioms sparse_no_transversal
/-- The proper-transversal criterion is not necessary even when the right
adjoint is known to be K4-free AND countably edge-coverable. This separate
example uses the one-step arc/right round trip. -/
theorem covered_right_no_transversal :
    ∃ (V : Type) (H : SimpleGraph V), (right H).CliqueFree 4 ∧
      IsCountableUnionOfTriangleFree (right H) ∧ ¬CountablyProperTransversal H := by
  obtain ⟨A,oA,hA,hcov,hRam⟩ := shift_vertex_ramsey (Set ℕ)
  letI : LinearOrder A := oA
  let G := Erdos595MiddleCorner.graph A
  exact ⟨_,arcGraph G,Erdos595ArcRoundTrip.right_arc_cliqueFree G hA,
    Erdos595ArcRoundTrip.right_arc_cover G hcov,
    no_transversal_of_hom G (arcGraph G) hRam (unit G)⟩

#print axioms covered_right_no_transversal

/-- The failure of the transversal criterion occurs even when the FULL
second right graph in the sparse normal form is known to be covered. -/
theorem sparse_covered_no_transversal :
    ∃ (V : Type) (H : SimpleGraph V), SparseTriangleBase H ∧
      (right (right H)).CliqueFree 4 ∧
      IsCountableUnionOfTriangleFree (right (right H)) ∧
      ¬CountablyProperTransversal (right H) := by
  obtain ⟨V,G,_,hc,h4,hn⟩ := covered_source_no_transversal
  exact ⟨_,arcGraph (arcGraph G),second_arc_sparse G,h4,
    Erdos595SecondArcCover.twice_cover G hc,hn⟩

#print axioms sparse_covered_no_transversal

end Erdos595SparseTransversalObstruction
