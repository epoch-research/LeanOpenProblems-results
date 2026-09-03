import Submission.Work

/-! Adding a square need not have diminishing returns, even between bipartite even graphs.
The final graph is not an even-minimal core. This is not a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SquareMarginal
open Critical EvenCore Rigidity
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def baseEdges : List (Sym2 (Fin 11)) := [s(0,1), s(1,2), s(2,3), s(3,0), s(0,4), s(4,5), s(5,6), s(6,0)]
def base : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet {e | e ∈ baseEdges}
def otherEdges : List (Sym2 (Fin 11)) := [s(1,7), s(7,6), s(6,8), s(8,1)]
def other : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet {e | e ∈ otherEdges}
def squareEdges : List (Sym2 (Fin 11)) := [s(1,9), s(9,4), s(4,10), s(10,1)]
def square : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet {e | e ∈ squareEdges}
def withOther : SimpleGraph (Fin 11) := base ⊔ other
def withSquare : SimpleGraph (Fin 11) := base ⊔ square
def full : SimpleGraph (Fin 11) := base ⊔ other ⊔ square
instance : DecidableRel base.Adj := by unfold base; infer_instance
lemma base_even : ∀ v, Even (base.degree v) := by decide +kernel
instance : DecidableRel other.Adj := by unfold other; infer_instance
lemma other_even : ∀ v, Even (other.degree v) := by decide +kernel
instance : DecidableRel square.Adj := by unfold square; infer_instance
lemma square_even : ∀ v, Even (square.degree v) := by decide +kernel
instance : DecidableRel withOther.Adj := by unfold withOther; infer_instance
lemma withOther_even : ∀ v, Even (withOther.degree v) := by decide +kernel
instance : DecidableRel withSquare.Adj := by unfold withSquare; infer_instance
lemma withSquare_even : ∀ v, Even (withSquare.degree v) := by decide +kernel
instance : DecidableRel full.Adj := by unfold full; infer_instance
lemma full_even : ∀ v, Even (full.degree v) := by decide +kernel

def b0 : base.Walk 0 0 :=
  .cons (show base.Adj 0 1 by decide +kernel) (.cons (show base.Adj 1 2 by decide +kernel) (.cons (show base.Adj 2 3 by decide +kernel) (.cons (show base.Adj 3 0 by decide +kernel) (.nil))))
lemma b0_cycle : b0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def b1 : base.Walk 0 0 :=
  .cons (show base.Adj 0 4 by decide +kernel) (.cons (show base.Adj 4 5 by decide +kernel) (.cons (show base.Adj 5 6 by decide +kernel) (.cons (show base.Adj 6 0 by decide +kernel) (.nil))))
lemma b1_cycle : b1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def t0 : withOther.Walk 0 0 :=
  .cons (show withOther.Adj 0 1 by decide +kernel) (.cons (show withOther.Adj 1 7 by decide +kernel) (.cons (show withOther.Adj 7 6 by decide +kernel) (.cons (show withOther.Adj 6 5 by decide +kernel) (.cons (show withOther.Adj 5 4 by decide +kernel) (.cons (show withOther.Adj 4 0 by decide +kernel) (.nil))))))
lemma t0_cycle : t0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def t1 : withOther.Walk 0 0 :=
  .cons (show withOther.Adj 0 3 by decide +kernel) (.cons (show withOther.Adj 3 2 by decide +kernel) (.cons (show withOther.Adj 2 1 by decide +kernel) (.cons (show withOther.Adj 1 8 by decide +kernel) (.cons (show withOther.Adj 8 6 by decide +kernel) (.cons (show withOther.Adj 6 0 by decide +kernel) (.nil))))))
lemma t1_cycle : t1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def s0 : withSquare.Walk 0 0 :=
  .cons (show withSquare.Adj 0 1 by decide +kernel) (.cons (show withSquare.Adj 1 9 by decide +kernel) (.cons (show withSquare.Adj 9 4 by decide +kernel) (.cons (show withSquare.Adj 4 0 by decide +kernel) (.nil))))
lemma s0_cycle : s0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def s1 : withSquare.Walk 0 0 :=
  .cons (show withSquare.Adj 0 3 by decide +kernel) (.cons (show withSquare.Adj 3 2 by decide +kernel) (.cons (show withSquare.Adj 2 1 by decide +kernel) (.cons (show withSquare.Adj 1 10 by decide +kernel) (.cons (show withSquare.Adj 10 4 by decide +kernel) (.cons (show withSquare.Adj 4 5 by decide +kernel) (.cons (show withSquare.Adj 5 6 by decide +kernel) (.cons (show withSquare.Adj 6 0 by decide +kernel) (.nil))))))))
lemma s1_cycle : s1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def sq : full.Walk 1 1 :=
  .cons (show full.Adj 1 9 by decide +kernel) (.cons (show full.Adj 9 4 by decide +kernel) (.cons (show full.Adj 4 10 by decide +kernel) (.cons (show full.Adj 10 1 by decide +kernel) (.nil))))
lemma sq_cycle : sq.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def osq : full.Walk 1 1 :=
  .cons (show full.Adj 1 7 by decide +kernel) (.cons (show full.Adj 7 6 by decide +kernel) (.cons (show full.Adj 6 8 by decide +kernel) (.cons (show full.Adj 8 1 by decide +kernel) (.nil))))
lemma osq_cycle : osq.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def avoid : full.Walk 0 0 :=
  .cons (show full.Adj 0 4 by decide +kernel) (.cons (show full.Adj 4 5 by decide +kernel) (.cons (show full.Adj 5 6 by decide +kernel) (.cons (show full.Adj 6 0 by decide +kernel) (.nil))))
lemma avoid_cycle : avoid.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

lemma base_number : number base = 2 := by
  have hu : number base ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles b0 b1 b0_cycle b1_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound base 0
  have hd : base.degree 0 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

lemma withOther_number : number withOther = 2 := by
  have hu : number withOther ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles t0 t1 t0_cycle t1_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound withOther 0
  have hd : withOther.degree 0 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

lemma withSquare_number : number withSquare = 2 := by
  have hu : number withSquare ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles s0 s1 s0_cycle s1_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound withSquare 0
  have hd : withSquare.degree 0 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

def color : Fin 11 → Bool := ![true,false,true,false,false,true,false,true,true,true,true]
lemma full_bipartite : ∀ u v, full.Adj u v → color u ≠ color v := by decide +kernel
lemma other_square : osq.IsCycle ∧ osq.length = 4 ∧ osq.toSubgraph.spanningCoe = other := by
  refine ⟨osq_cycle,by decide +kernel,?_⟩
  ext u v
  change s(u,v) ∈ osq.toSubgraph.edgeSet ↔ other.Adj u v
  rw [osq.mem_edges_toSubgraph]
  revert u v
  decide +kernel

lemma square_graph : sq.toSubgraph.spanningCoe = square := by
  ext u v
  change s(u,v) ∈ sq.toSubgraph.edgeSet ↔ square.Adj u v
  rw [sq.mem_edges_toSubgraph]
  revert u v
  decide +kernel
lemma square_length : sq.length = 4 := by decide +kernel
lemma delete_square : full \ sq.toSubgraph.spanningCoe = withOther := by
  rw [square_graph]
  ext u v
  revert u v
  decide +kernel
lemma full_number : number full = 3 := by
  have hu := number_restore_cycle sq_cycle
  rw [delete_square,withOther_number] at hu
  have hl := StarCore.number_degree_bound full 1
  have hd : full.degree 1 = 6 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

lemma disjoint_increments :
    Disjoint base.edgeSet other.edgeSet ∧ Disjoint base.edgeSet square.edgeSet ∧
      Disjoint other.edgeSet square.edgeSet := by
  repeat' apply And.intro
  all_goals
    rw [Set.disjoint_left]
    decide +kernel

/-- A square's marginal cost can increase when an edge-disjoint square is added. -/
lemma square_diminishing_returns_false :
    (∀ v, Even (base.degree v)) ∧ (∀ v, Even (withOther.degree v)) ∧
    base ≤ withOther ∧ Disjoint withOther.edgeSet square.edgeSet ∧
    sq.IsCycle ∧ sq.length = 4 ∧ sq.toSubgraph.spanningCoe = square ∧
    number (base ⊔ square) + number withOther <
      number base + number (withOther ⊔ square) := by
  refine ⟨base_even,withOther_even,le_sup_left,?_,sq_cycle,square_length,square_graph,?_⟩
  · rw [Set.disjoint_left]
    decide +kernel
  · change number withSquare + number withOther < number base + number full
    rw [withSquare_number,withOther_number,base_number,full_number]
    omega

/-- The example does not violate any hypothesis restricted to minimal cores. -/
lemma full_not_minimal : ¬ EvenMinimal full := by
  intro hm
  have he : ∀ v, Even (full.degree v) := full_even
  have hs : full.degree 1 = 2 * number full := by
    rw [full_number]
    decide +kernel
  have ha := (StarCore.EvenMinimal.saturated_vertex (G := full) hm (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using he v) 1 (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hs)).1
  have hhit := (StarCore.cycle_hits_iff_induce_acyclic (G := full) 1).mpr ha
  have h := hhit 0 avoid avoid_cycle
  exact (show (1 : Fin 11) ∉ avoid.support by decide +kernel) h

#print axioms square_diminishing_returns_false
#print axioms full_not_minimal
end Erdos184Work.SquareMarginal
