import Submission.GraphVertexSeparation

/-! An obstruction to an UNRESTRICTED local repair inequality. The source lacks
 two of the K₂,₃ edges needed in the dominated repair proposal. This does not
 disprove that proposal or the original Erdős 184 conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UnrestrictedRepairObstruction
open Critical
set_option maxHeartbeats 1000000
abbrev V := Fin 9

def source : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,2),(0,3),(0,7),(0,8),(1,3),(1,4),(1,7),(1,8),(2,6),(3,5),(3,6),(4,5)] : List (V × V)))
instance : DecidableRel source.Adj := by unfold source; infer_instance

def target : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,1),(0,3),(0,7),(0,8),(1,3),(1,7),(1,8),(2,3),(2,6),(3,4),(3,5),(3,6),(4,5)] : List (V × V)))
instance : DecidableRel target.Adj := by unfold target; infer_instance

def left : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(2,3),(2,6),(3,6)] : List (V × V)))
instance : DecidableRel left.Adj := by unfold left; infer_instance

def right : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(3,4),(3,5),(4,5)] : List (V × V)))
instance : DecidableRel right.Adj := by unfold right; infer_instance

def middle : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,1),(0,3),(0,7),(0,8),(1,3),(1,7),(1,8)] : List (V × V)))
instance : DecidableRel middle.Adj := by unfold middle; infer_instance

def removed : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,2),(1,4)] : List (V × V)))
instance : DecidableRel removed.Adj := by unfold removed; infer_instance

def added : SimpleGraph V := SimpleGraph.fromRel (fun x y =>
  (x,y) ∈ ([(0,1),(2,3),(3,4)] : List (V × V)))
instance : DecidableRel added.Adj := by unfold added; infer_instance

def p : source.Walk 3 3 :=
  .cons (show source.Adj 3 0 by decide +kernel) (.cons (show source.Adj 0 7 by decide +kernel) (.cons (show source.Adj 7 1 by decide +kernel) (.cons (show source.Adj 1 4 by decide +kernel) (.cons (show source.Adj 4 5 by decide +kernel) (.cons (show source.Adj 5 3 by decide +kernel) (.nil))))))
lemma p_cycle : p.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def q : source.Walk 3 3 :=
  .cons (show source.Adj 3 1 by decide +kernel) (.cons (show source.Adj 1 8 by decide +kernel) (.cons (show source.Adj 8 0 by decide +kernel) (.cons (show source.Adj 0 2 by decide +kernel) (.cons (show source.Adj 2 6 by decide +kernel) (.cons (show source.Adj 6 3 by decide +kernel) (.nil))))))
lemma q_cycle : q.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def a : left.Walk 3 3 :=
  .cons (show left.Adj 3 2 by decide +kernel) (.cons (show left.Adj 2 6 by decide +kernel) (.cons (show left.Adj 6 3 by decide +kernel) (.nil)))
lemma a_cycle : a.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def b : right.Walk 3 3 :=
  .cons (show right.Adj 3 4 by decide +kernel) (.cons (show right.Adj 4 5 by decide +kernel) (.cons (show right.Adj 5 3 by decide +kernel) (.nil)))
lemma b_cycle : b.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def c : middle.Walk 0 0 :=
  .cons (show middle.Adj 0 1 by decide +kernel) (.cons (show middle.Adj 1 7 by decide +kernel) (.cons (show middle.Adj 7 0 by decide +kernel) (.nil)))
lemma c_cycle : c.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def d : middle.Walk 0 0 :=
  .cons (show middle.Adj 0 3 by decide +kernel) (.cons (show middle.Adj 3 1 by decide +kernel) (.cons (show middle.Adj 1 8 by decide +kernel) (.cons (show middle.Adj 8 0 by decide +kernel) (.nil))))
lemma d_cycle : d.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

lemma source_even : ∀ v : V, Even (source.degree v) := by decide +kernel
lemma left_even : ∀ v : V, Even (left.degree v) := by decide +kernel
lemma right_even : ∀ v : V, Even (right.degree v) := by decide +kernel
lemma middle_even : ∀ v : V, Even (middle.degree v) := by decide +kernel

lemma source_number : number source = 2 := by
  have hu : number source ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles p q p_cycle q_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound source 3
  have hd : source.degree 3 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

lemma left_number : number left = 1 := by
  have hh := GraphCircuitCode.cycle_number_one a.toSubgraph (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular left a_cycle)
  have he : a.toSubgraph.spanningCoe = left := by
    ext x y
    change s(x,y) ∈ a.toSubgraph.edgeSet ↔ left.Adj x y
    rw [a.mem_edges_toSubgraph]
    revert x y
    decide +kernel
  rwa [he] at hh

lemma right_number : number right = 1 := by
  have hh := GraphCircuitCode.cycle_number_one b.toSubgraph (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular right b_cycle)
  have he : b.toSubgraph.spanningCoe = right := by
    ext x y
    change s(x,y) ∈ b.toSubgraph.edgeSet ↔ right.Adj x y
    rw [b.mem_edges_toSubgraph]
    revert x y
    decide +kernel
  rwa [he] at hh

lemma middle_number : number middle = 2 := by
  have hu : number middle ≤ 2 := by
    apply LocalObstruction.number_le_two_cycles c d c_cycle d_cycle
    · apply List.disjoint_toFinset_iff_disjoint.mp
      decide +kernel
    · decide +kernel
  have hl := StarCore.number_degree_bound middle 0
  have hd : middle.degree 0 = 4 := by decide +kernel
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hd
  omega

lemma left_right_touch : GraphVertexSeparation.TouchAt left right 3 := by
  change ∀ x : V, (∃ y, left.Adj x y) → (∃ y, right.Adj x y) → x = 3
  decide +kernel
lemma middle_touch : GraphVertexSeparation.TouchAt (left ⊔ right) middle 3 := by
  change ∀ x : V, (∃ y, left.Adj x y ∨ right.Adj x y) →
    (∃ y, middle.Adj x y) → x = 3
  decide +kernel
lemma target_union : target = (left ⊔ right) ⊔ middle := by
  ext x y
  change target.Adj x y ↔ (left.Adj x y ∨ right.Adj x y) ∨ middle.Adj x y
  revert x y
  decide +kernel

lemma target_number : number target = 4 := by
  have hL : ∀ v, Even (Nat.card (left.neighborSet v)) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using left_even
  have hR : ∀ v, Even (Nat.card (right.neighborSet v)) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using right_even
  have hM : ∀ v, Even (Nat.card (middle.neighborSet v)) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using middle_even
  have he : ∀ v, Even (Nat.card ((left ⊔ right).neighborSet v)) := by
    have hh := GraphVertexSeparation.even_sup_of_disjoint left_right_touch.edge_disjoint
      (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hL)
      (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hR)
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hh
  have h1 := GraphVertexSeparation.number_sup left_right_touch
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hL)
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hR)
  have h2 := GraphVertexSeparation.number_sup middle_touch
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using he)
    (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hM)
  rw [← target_union, h1, left_number, right_number, middle_number] at h2
  exact h2

lemma target_repair : target = (source \ removed) ⊔ added := by
  ext x y
  change target.Adj x y ↔ (source.Adj x y ∧ ¬ removed.Adj x y) ∨ added.Adj x y
  revert x y
  decide +kernel

/-- The source is even and contains ua,ub,vb,vc, and the three new edges
are absent. These four old edges alone do NOT justify a loss-one bound. -/
lemma obstruction :
    (∀ v : V, Even (source.degree v)) ∧
    source.Adj 0 2 ∧ source.Adj 0 3 ∧ source.Adj 1 3 ∧ source.Adj 1 4 ∧
    ¬ source.Adj 0 1 ∧ ¬ source.Adj 2 3 ∧ ¬ source.Adj 3 4 ∧
    number source + 1 < number ((source \ removed) ⊔ added) := by
  refine ⟨source_even, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  rw [← target_repair, source_number, target_number]
  omega

/-- The common-neighbor hypotheses of the dominated repair are absent. -/
lemma missing_common_edges : ¬ source.Adj 0 4 ∧ ¬ source.Adj 1 2 := by decide +kernel

end Erdos184Work.UnrestrictedRepairObstruction
#print axioms Erdos184Work.UnrestrictedRepairObstruction.obstruction
#print axioms Erdos184Work.UnrestrictedRepairObstruction.target_number
