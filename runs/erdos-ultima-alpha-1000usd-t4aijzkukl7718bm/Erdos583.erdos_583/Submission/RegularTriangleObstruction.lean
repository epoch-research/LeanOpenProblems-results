import Submission.RegularSparseZeroNormalization

/-! A counterexample to budget-free triangle repair, NOT to Gallai.
K5 minus one edge has a regular two-trail family but needs three paths. -/
namespace Erdos583RegularTriangleObstructionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583RegularRootedCutDevelopment Erdos583RegularFlowerExposuresDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

abbrev edges : Finset (Sym2 (Fin 5)) :=
  {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4)}
def G : SimpleGraph (Fin 5) := fromEdgeSet (edges : Set (Sym2 (Fin 5)))
instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edges : Set (Sym2 (Fin 5)))).Adj)

def C : G.Walk 0 0 := .cons (by decide : G.Adj 0 1)
  (.cons (by decide : G.Adj 1 2) (.cons (by decide : G.Adj 2 3)
    (.cons (by decide : G.Adj 3 0) .nil)))
def e : G.Walk 0 4 := .cons (by decide : G.Adj 0 4) .nil
def p : G.Walk 0 4 := C.append e
def q : G.Walk 0 3 := .cons (by decide : G.Adj 0 2)
  (.cons (by decide : G.Adj 2 4) (.cons (by decide : G.Adj 4 1)
    (.cons (by decide : G.Adj 1 3) .nil)))
abbrev starts : Fin 2 → Fin 5 := ![0,0]
abbrev finishes : Fin 2 → Fin 5 := ![4,3]
def walks : ∀ i, G.Walk (starts i) (finishes i) :=
  Fin.cases p (Fin.cases q (fun i ↦ Fin.elim0 i))
def T : TrailFamily G 2 where
  start := starts
  finish := finishes
  walk := walks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro d hd he
    simp only [Walk.mem_edges_toSubgraph] at hd he
    have h : ∀ i j : Fin 2, i ≠ j → ∀ d : Sym2 (Fin 5),
        d ∈ (walks i).edges → d ∉ (walks j).edges := by decide
    exact h i j hij d hd he
  cover := by
    intro d
    induction d using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

def tails : ∀ s : Fin 2 × Bool, G.Walk (T.endpoint s) 0
  | (0,false) => e.reverse
  | (0,true) => C
  | (1,false) => q.reverse
  | (1,true) => .nil

def R : RootedCut T 0 Finset.univ where
  tail := fun s ↦ tails s.val
  trail := by
    intro s
    have h : ∀ s, (tails s).IsTrail := by
      intro s
      simp only [Walk.isTrail_def]
      revert s
      decide
    exact h s.val
  disjoint := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro d hd he
    change d ∈ (tails s.val).toSubgraph.edgeSet at hd
    change d ∈ (tails t.val).toSubgraph.edgeSet at he
    simp only [Walk.mem_edges_toSubgraph] at hd he
    have h : ∀ s t : Fin 2 × Bool, s ≠ t → ∀ d : Sym2 (Fin 5),
        d ∈ (tails s).edges → d ∉ (tails t).edges := by decide
    exact h s.val t.val (fun hh ↦ hst (Subtype.ext hh)) d hd he
  decomp := by
    intro i hi
    fin_cases i
    · change p.toSubgraph=C.toSubgraph ⊔ e.reverse.toSubgraph
      simp only [p,Walk.toSubgraph_append,Walk.toSubgraph_reverse]
    · change q.toSubgraph=(Walk.nil : G.Walk 0 0).toSubgraph ⊔ q.reverse.toSubgraph
      rw [Walk.toSubgraph_reverse]
      exact (sup_eq_right.mpr ((G.singletonSubgraph_le_iff 0 q.toSubgraph).mpr
        (q.mem_verts_toSubgraph.mpr q.start_mem_support))).symm
  outside := by simp

lemma regular : RegularlyRooted T 0 := by
  refine ⟨Finset.univ,R,?_,?_,?_⟩
  · intro s
    change RegularTail (tails s.val)
    rcases s with ⟨⟨i,b⟩,hi⟩
    fin_cases i <;> cases b
    · apply Or.inl
      change e.reverse.IsPath
      rw [Walk.isPath_def]
      decide
    · apply Or.inr
      refine ⟨rfl,?_⟩
      change C.toSubgraph.verts.ncard=C.length
      simp [C,Set.ncard_eq_toFinset_card']
    · apply Or.inl
      change q.reverse.IsPath
      rw [Walk.isPath_def]
      decide
    · apply Or.inl
      change (Walk.nil : G.Walk 0 0).IsPath
      rw [Walk.isPath_def]
      decide
  · intro i hi
    fin_cases i
    · change C.toSubgraph.verts ∩ e.reverse.toSubgraph.verts ⊆ {0}
      simp [C,e,Set.subset_def]
    · change (Walk.nil : G.Walk 0 0).toSubgraph.verts ∩ q.reverse.toSubgraph.verts ⊆ {0}
      exact Set.inter_subset_left
  · simp

lemma zero_set : {v | T.quota v=0}=({1,2} : Set (Fin 5)) := by
  ext v
  change T.quota v=0 ↔ v=1 ∨ v=2
  rw [TrailFamily.quota,Nat.card_eq_fintype_card]
  revert v
  decide

lemma root_quota : T.quota 0=2 := by
  rw [TrailFamily.quota,Nat.card_eq_fintype_card]
  decide

lemma edge_card : G.edgeSet.ncard=9 := by
  rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
  decide

lemma connected : G.Connected := by
  have hm (v : Fin 5) : v ∈ q.support := by revert v; decide
  exact ⟨fun u v ↦ (q.takeUntil u (hm u)).reachable.symm.trans
    (q.takeUntil v (hm v)).reachable⟩

lemma one_defect : T.score+1=G.edgeSet.ncard+2 := by
  have hs : T.score=10 := by
    simp [TrailFamily.score,T,walks,p,C,e,q,Fin.sum_univ_succ,Walk.verts_toSubgraph]
    simp only [Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
    decide
  rw [hs,edge_card]

lemma no_two_paths : ¬∃ P : TrailFamily G 2, ∀ i, (P.walk i).IsPath := by
  rintro ⟨P,hP⟩
  have he := P.score_eq_edges_add_iff.mpr hP
  have hb := P.score_le
  rw [edge_card] at he
  norm_num at hb
  omega

/-- This is a disproof of bare local repair, not of erdos_583. The budget
here is two, strictly below the conjectured ceiling for five vertices. -/
lemma budget_free_triangle_repair_false :
    ¬(∀ (S : TrailFamily G 2) (r : Fin 5), RegularlyRooted S r →
      {z | S.quota z=0}.ncard ≤ 2 → 2 ≤ S.quota r →
      ∃ P : TrailFamily G 2, ∀ i, (P.walk i).IsPath) := by
  intro h
  apply no_two_paths
  exact h T 0 regular (by rw [zero_set]; simp) (by rw [root_quota])

end Erdos583RegularTriangleObstructionDevelopment
