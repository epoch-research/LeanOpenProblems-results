import Submission.Work

/-! A score-preserving rooted-tail pivot can lose terminality of a
triangle-free marked edge, even when deleting that edge leaves a connected
graph. This is not a counterexample to a global selection theorem or to Gallai. -/
open SimpleGraph Erdos583Work
namespace Erdos583TerminalPivotObstructionDevelopment
set_option maxHeartbeats 1200000

abbrev edges : Finset (Sym2 (Fin 8)) :=
  {s(0,1),s(1,2),s(2,3),s(3,0),s(0,6),s(1,4),s(4,5),s(5,0),s(0,7),s(2,5),s(3,4)}

def G : SimpleGraph (Fin 8) := fromEdgeSet (edges : Set (Sym2 (Fin 8)))
instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edges : Set (Sym2 (Fin 8)))).Adj)

def F : SimpleGraph (Fin 8) := fromEdgeSet ({s(1,4)} : Set (Sym2 (Fin 8)))
instance : DecidableRel F.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet ({s(1,4)} : Set (Sym2 (Fin 8)))).Adj)

lemma structural : (∀ v, Odd (G.degree v)) ∧ F ≤ G ∧
    (∀ v, (F.neighborSet v).Subsingleton) ∧ (G \ F).Connected ∧
    TriangleFreeMatching.TriangleFreeEdges G F := by
  refine ⟨by decide,?_,?_,by decide,?_⟩
  · change ∀ a b, F.Adj a b → G.Adj a b
    decide
  · intro v x hx y hy
    revert v x y
    decide
  · intro a b hab x
    revert a b x
    decide

def p : G.Walk 0 6 := .cons (by decide : G.Adj 0 1)
  (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 3)
    (.cons (by decide : G.Adj 3 0) (.cons (by decide : G.Adj 0 6) .nil))))
def q : G.Walk 1 7 := .cons (by decide : G.Adj 1 4)
  (.cons (by decide : G.Adj 4 5) (.cons (by decide : G.Adj 5 0)
    (.cons (by decide : G.Adj 0 7) .nil)))
def r : G.Walk 2 5 := .cons (by decide : G.Adj 2 5) .nil
def s : G.Walk 3 4 := .cons (by decide : G.Adj 3 4) .nil

def p' : G.Walk 1 6 := .cons (by decide : G.Adj 1 2)
  (.cons (by decide : G.Adj 2 3) (.cons (by decide : G.Adj 3 0)
    (.cons (by decide : G.Adj 0 6) .nil)))
def q' : G.Walk 0 7 := .cons (by decide : G.Adj 0 5)
  (.cons (by decide : G.Adj 5 4) (.cons (by decide : G.Adj 4 1)
    (.cons (by decide : G.Adj 1 0) (.cons (by decide : G.Adj 0 7) .nil))))

abbrev starts : Fin 4 → Fin 8 := ![0,1,2,3]
abbrev starts' : Fin 4 → Fin 8 := ![1,0,2,3]
abbrev finishes : Fin 4 → Fin 8 := ![6,7,5,4]

def walks : ∀ i, G.Walk (starts i) (finishes i) :=
  Fin.cases p (Fin.cases q (Fin.cases r (Fin.cases s (fun i ↦ Fin.elim0 i))))

def walks' : ∀ i, G.Walk (starts' i) (finishes i) :=
  Fin.cases p' (Fin.cases q' (Fin.cases r (Fin.cases s (fun i ↦ Fin.elim0 i))))

def T : NormalTrailSystem G 4 where
  start := starts
  finish := finishes
  walk := walks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  endpoint_bijective := by decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 4, i ≠ j → ∀ e : Sym2 (Fin 8),
        e ∈ (walks i).edges → e ∉ (walks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

def U : NormalTrailSystem G 4 where
  start := starts'
  finish := finishes
  walk := walks'
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  endpoint_bijective := by decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 4, i ≠ j → ∀ e : Sym2 (Fin 8),
        e ∈ (walks' i).edges → e ∉ (walks' j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

/-- The marked edge is first or last in the stored walk. -/
def Terminal {a b : Fin 8} (w : G.Walk a b) : Prop :=
  w.edges.head?=some s(1,4) ∨ w.edges.getLast?=some s(1,4)

lemma terminality_lost : Terminal (T.walk 1) ∧ ∀ i, ¬Terminal (U.walk i) := by
  simp only [Terminal]
  decide

lemma same_score : T.score=14 ∧ U.score=14 := by
  simp [NormalTrailSystem.score,T,U,Fin.sum_univ_succ,walks,walks',p,q,r,s,p',q',
    Walk.verts_toSubgraph]
  simp only [Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
  decide

/-- The two changed members are exactly the local rooted-tail replacement:
remove 0-1 from the closed root prefix and reverse the new 0-1-(1-4-5-0)
closed prefix, retaining the respective 0-6 and 0-7 suffixes. -/
lemma pivot_forms :
    p = (Walk.cons (by decide : G.Adj 0 1)
      (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 3)
        (.cons (by decide : G.Adj 3 0) .nil)))).concat (by decide : G.Adj 0 6) ∧
    q' = ((Walk.cons (by decide : G.Adj 0 1)
      (.cons (by decide : G.Adj 1 4) (.cons (by decide : G.Adj 4 5)
        (.cons (by decide : G.Adj 5 0) .nil)))).reverse).concat (by decide : G.Adj 0 7) := by
  decide

lemma terminal_vertices_table :
    (∀ i, MatchingTrim.terminalVertices (T.walk i).toSubgraph F =
      if i=1 then {1} else ∅) ∧
    ∀ i, MatchingTrim.terminalVertices (U.walk i).toSubgraph F=∅ := by
  classical
  constructor
  · intro i
    ext x
    simp only [MatchingTrim.terminalVertices,Finset.mem_filter,Finset.mem_univ,true_and,
      Subgraph.neighborSet,neighborSet,inf_adj,Subgraph.spanningCoe_adj,
      Walk.adj_toSubgraph_iff_mem_edges,Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
    revert i x
    decide
  · intro i
    ext x
    simp only [MatchingTrim.terminalVertices,Finset.mem_filter,Finset.mem_univ,true_and,
      Subgraph.neighborSet,neighborSet,inf_adj,Subgraph.spanningCoe_adj,
      Walk.adj_toSubgraph_iff_mem_edges,Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
    revert i x
    decide

lemma terminal_weight_lost : MatchingTrim.terminalWeight T.parts F=1 ∧
    MatchingTrim.terminalWeight U.parts F=0 := by
  classical
  have hs (X : NormalTrailSystem G 4) : MatchingTrim.terminalWeight X.parts F=
      ∑ i, (MatchingTrim.terminalVertices (X.walk i).toSubgraph F).card := by
    unfold MatchingTrim.terminalWeight NormalTrailSystem.parts
    rw [Finset.sum_image]
    intro i _ j _ heq
    exact X.subgraph_injective heq
  simp only [hs,terminal_vertices_table.1,terminal_vertices_table.2]
  simp [Fin.sum_univ_succ]

end Erdos583TerminalPivotObstructionDevelopment
