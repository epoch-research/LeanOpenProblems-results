import Submission.Work

/-! A single INTERNAL defect need not be normalizable at fixed endpoint quotas,
even at the Gallai budget, with normal quotas and an even-induced tree.
This is an obstruction to an auxiliary strategy, not to Gallai's conjecture. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootCapacity
namespace Erdos583InternalDefectObstructionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma path_family_cut_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (S : Finset V) (v : V) (hv : v ∉ S) :
    Nat.card (G.neighborSet v)+T.quota v+∑ w ∈ S, T.quota w ≤
      2*k+(boundaryGraph G (S : Set V)).edgeSet.ncard := by
  classical
  let C := (boundaryGraph G (S : Set V)).edgeSet
  have hlocal (j : Fin k) :
      ((T.walk j).toSubgraph.neighborSet v).ncard +
        ((if T.start j=v then 1 else 0)+(if T.finish j=v then 1 else 0)) +
        (∑ w ∈ S, ((if T.start j=w then 1 else 0)+(if T.finish j=w then 1 else 0))) ≤
        2+((T.walk j).toSubgraph.edgeSet ∩ C).ncard := by
    rw [path_incidence (T.walk j) (hp j) v,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq]
    by_cases hvm : v ∈ (T.walk j).support
    · have hh := trail_endpoint_boundary_bound (S : Set V) (T.walk j) (T.isTrail j) hvm hv
      rw [if_pos hvm]
      simp only [Finset.mem_coe] at hh
      dsimp only [C] at *
      omega
    · rw [if_neg hvm]
      split_ifs <;> omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hlocal j)
  have hsub : C ⊆ G.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b => exact he.1
  have hC := ncard_inter_eq_sum T C
  rw [Set.inter_eq_right.mpr hsub] at hC
  have hend : ∑ w ∈ S, T.quota w = ∑ j, ∑ w ∈ S,
      ((if T.start j=w then 1 else 0)+(if T.finish j=w then 1 else 0)) := by
    simp_rw [quota_eq_sum_endpoints]
    rw [Finset.sum_comm]
  have hquota := quota_eq_sum_endpoints T v
  simp only [Finset.sum_add_distrib] at hh hquota hend
  rw [←QuotaParity.degree_sum T v,←hquota,←hend,←hC] at hh
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm] using hh

abbrev edges : Finset (Sym2 (Fin 12)) :=
  {s(0,7),s(0,1),s(1,2),s(2,0),s(0,6),s(1,3),s(3,0),s(0,4),s(4,5),
   s(7,8),s(8,9),s(9,10),s(10,11)}

def G : SimpleGraph (Fin 12) := fromEdgeSet (edges : Set (Sym2 (Fin 12)))
instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edges : Set (Sym2 (Fin 12)))).Adj)

abbrev evenVerts : Finset (Fin 12) := {0,2,3,4,7,8,9,10}
abbrev zeros : Finset (Fin 12) := {0,2,3,4}
abbrev outside : Finset (Fin 12) := {7,8,9,10,11}

lemma connected : G.Connected := by decide

lemma even_forest : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic := by
  have he : {v : Fin 12 | Even (Nat.card (G.neighborSet v))}=(evenVerts : Set (Fin 12)) := by
    ext v
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Set.mem_setOf_eq,Finset.mem_coe]
    revert v
    decide
  rw [he]
  apply (isTree_iff_connected_and_card.mpr ⟨by decide,?_⟩).IsAcyclic
  rw [Nat.card_eq_fintype_card,←edgeFinset_card,Nat.card_eq_fintype_card]
  decide

lemma zero_forest : (G.induce (zeros : Set (Fin 12))).IsAcyclic := by
  apply (isTree_iff_connected_and_card.mpr ⟨by decide,?_⟩).IsAcyclic
  rw [Nat.card_eq_fintype_card,←edgeFinset_card,Nat.card_eq_fintype_card]
  decide

def p : G.Walk 7 6 := .cons (by decide : G.Adj 7 0)
  (.cons (by decide : G.Adj 0 1) (.cons (by decide : G.Adj 1 2)
    (.cons (by decide : G.Adj 2 0) (.cons (by decide : G.Adj 0 6) .nil))))
def q : G.Walk 1 5 := .cons (by decide : G.Adj 1 3)
  (.cons (by decide : G.Adj 3 0) (.cons (by decide : G.Adj 0 4)
    (.cons (by decide : G.Adj 4 5) .nil)))
def a : G.Walk 7 8 := .cons (by decide : G.Adj 7 8) .nil
def b : G.Walk 8 9 := .cons (by decide : G.Adj 8 9) .nil
def c : G.Walk 9 10 := .cons (by decide : G.Adj 9 10) .nil
def d : G.Walk 10 11 := .cons (by decide : G.Adj 10 11) .nil

abbrev starts : Fin 6 → Fin 12 := ![7,1,7,8,9,10]
abbrev finishes : Fin 6 → Fin 12 := ![6,5,8,9,10,11]
def walks : ∀ i, G.Walk (starts i) (finishes i) :=
  Fin.cases p (Fin.cases q (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun i ↦ Fin.elim0 i))))))

def T : TrailFamily G 6 where
  start := starts
  finish := finishes
  walk := walks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 6, i ≠ j → ∀ e : Sym2 (Fin 12),
        e ∈ (walks i).edges → e ∉ (walks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

abbrev quota : Fin 12 → ℕ := ![0,1,0,0,0,1,1,2,2,2,2,1]

lemma quota_table (v : Fin 12) : T.quota v=quota v := by
  rw [quota_eq_sum_endpoints]
  fin_cases v <;> norm_num [T, starts, finishes, quota, Fin.sum_univ_succ] <;> simp (disch := decide)

lemma quota_zero_set : {v | T.quota v=0}=(zeros : Set (Fin 12)) := by
  ext v
  rw [Set.mem_setOf_eq,quota_table]
  revert v
  decide

lemma edge_card : G.edgeSet.ncard=13 := by
  rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,←edgeFinset_card]
  decide

lemma one_defect : T.score+1=G.edgeSet.ncard+6 := by
  rw [edge_card]
  simp [TrailFamily.score,T,walks,p,q,a,b,c,d,Fin.sum_univ_succ,Walk.verts_toSubgraph]
  simp only [Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
  decide

lemma no_positive_repeats : ∀ i v, 0 < T.quota v → (T.walk i).support.count v ≤ 1 := by
  simp_rw [quota_table]
  decide

lemma no_nil : ∀ i, ¬(T.walk i).Nil := by decide

lemma boundary : (boundaryGraph G (outside : Set (Fin 12))).edgeSet={s(0,7)} := by
  have he (p q : Prop) : p ≠ q ↔ ¬(p ↔ q) :=
    ⟨fun h hi ↦ h (propext hi),fun h hi ↦ h (hi ▸ Iff.rfl)⟩
  ext e
  induction e using Sym2.ind with
  | h a b =>
    change (G.Adj a b ∧ ((a ∈ outside) ≠ (b ∈ outside))) ↔
      s(a,b) ∈ ({s(0,7)} : Set (Sym2 (Fin 12)))
    rw [he]
    revert a b
    decide

lemma no_paths_with_same_quotas :
    ¬∃ U : TrailFamily G 6, (∀ v, U.quota v=T.quota v) ∧ ∀ i, (U.walk i).IsPath := by
  rintro ⟨U,hq,hp⟩
  have hh := path_family_cut_bound U hp outside 0 (by decide)
  simp_rw [hq,quota_table] at hh
  have hd : Nat.card (G.neighborSet 0)=6 := by
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    decide
  have hc : ∑ v ∈ outside, quota v=9 := by decide
  rw [hd,hc,boundary,Set.ncard_singleton] at hh
  norm_num [quota] at hh

lemma quota_le_two (v : Fin 12) : T.quota v ≤ 2 := by
  rw [quota_table]
  revert v
  decide

/-- Score maximality subject to prescribed quotas does not imply pathhood. -/
lemma constrained_maximum (U : TrailFamily G 6) (hq : ∀ v, U.quota v=T.quota v) :
    U.score ≤ T.score := by
  have hb := U.score_le_edges_add
  have hn : U.score ≠ G.edgeSet.ncard+6 := by
    intro hh
    exact no_paths_with_same_quotas ⟨U,hq,U.score_eq_edges_add_iff.mp hh⟩
  have ht := one_defect
  omega

/-- There is not even a rooted one-defect realization of these quotas. -/
lemma no_rooted_same_quotas :
    ¬∃ (U : TrailFamily G 6) (r : Fin 12), (∀ v, U.quota v=T.quota v) ∧
      U.score+1=G.edgeSet.ncard+6 ∧ HasRoot U r := by
  rintro ⟨U,r,hq,hs,hr⟩
  have hd : Nat.card (G.neighborSet 0)=6 := by
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    decide
  have hc : ∑ v ∈ outside, quota v=9 := by decide
  have he : r=0 := root_eq_of_cut_over_capacity U r hs hr outside 0 (by decide) (by
    simp_rw [hq,quota_table]
    rw [hd,hc,boundary,Set.ncard_singleton]
    norm_num [quota])
  have hh := RootEnergy.root_quota_pos hr
  rw [he,hq,quota_table] at hh
  norm_num [quota] at hh

-- A positive certificate for the original path-count question on this graph.
def goodP : G.Walk 11 2 := .cons (by decide : G.Adj 11 10)
  (.cons (by decide : G.Adj 10 9) (.cons (by decide : G.Adj 9 8)
    (.cons (by decide : G.Adj 8 7) (.cons (by decide : G.Adj 7 0)
      (.cons (by decide : G.Adj 0 3) (.cons (by decide : G.Adj 3 1)
        (.cons (by decide : G.Adj 1 2) .nil)))))))
def goodQ : G.Walk 2 6 := .cons (by decide : G.Adj 2 0)
  (.cons (by decide : G.Adj 0 6) .nil)
def goodR : G.Walk 1 5 := .cons (by decide : G.Adj 1 0)
  (.cons (by decide : G.Adj 0 4) (.cons (by decide : G.Adj 4 5) .nil))

abbrev goodStarts : Fin 3 → Fin 12 := ![11,2,1]
abbrev goodFinishes : Fin 3 → Fin 12 := ![2,6,5]
def goodWalks : ∀ i, G.Walk (goodStarts i) (goodFinishes i) :=
  Fin.cases goodP (Fin.cases goodQ (Fin.cases goodR (fun i ↦ Fin.elim0 i)))

def U : TrailFamily G 3 where
  start := goodStarts
  finish := goodFinishes
  walk := goodWalks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 3, i ≠ j → ∀ e : Sym2 (Fin 12),
        e ∈ (goodWalks i).edges → e ∉ (goodWalks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

lemma three_paths : ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 :=
  MatchingAppend.path_family_partition U (by intro i; simp only [Walk.isPath_def]; revert i; decide)

end Erdos583InternalDefectObstructionDevelopment
