import Submission.Work

/-! A rooted quota-one defect at the exact vertex budget with independent
even vertices need not be repairable at FIXED quotas. This is not a global
score maximum and is not a Gallai counterexample. -/
namespace Erdos583IndependentRootObstructionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootCapacity
open scoped Classical
set_option maxHeartbeats 1600000

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

abbrev edges : Finset (Sym2 (Fin 8)) :=
  {s(0,1),s(0,2),s(0,3),s(1,2),s(1,3),s(0,4),s(4,5),s(0,6),s(6,7)}
def G : SimpleGraph (Fin 8) := fromEdgeSet (edges : Set (Sym2 (Fin 8)))
instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (edges : Set (Sym2 (Fin 8)))).Adj)
abbrev outside : Finset (Fin 8) := {4,5,6,7}
abbrev evenVerts : Finset (Fin 8) := {2,3,4,6}

def p : G.Walk 0 6 := (.cons (by decide : G.Adj 0 2) (.cons (by decide : G.Adj 2 1) (.cons (by decide : G.Adj 1 3) (.cons (by decide : G.Adj 3 0) (.cons (by decide : G.Adj 0 6) .nil)))))
def q : G.Walk 1 4 := (.cons (by decide : G.Adj 1 0) (.cons (by decide : G.Adj 0 4) .nil))
def u : G.Walk 4 5 := (.cons (by decide : G.Adj 4 5) .nil)
def v : G.Walk 6 7 := (.cons (by decide : G.Adj 6 7) .nil)
def goodP : G.Walk 7 3 := (.cons (by decide : G.Adj 7 6) (.cons (by decide : G.Adj 6 0) (.cons (by decide : G.Adj 0 1) (.cons (by decide : G.Adj 1 3) .nil))))
def goodQ : G.Walk 3 1 := (.cons (by decide : G.Adj 3 0) (.cons (by decide : G.Adj 0 2) (.cons (by decide : G.Adj 2 1) .nil)))
def goodR : G.Walk 0 5 := (.cons (by decide : G.Adj 0 4) (.cons (by decide : G.Adj 4 5) .nil))

abbrev Starts : Fin 4 → Fin 8 := ![0,1,4,6]
abbrev Finishes : Fin 4 → Fin 8 := ![6,4,5,7]
def Walks : ∀ i, G.Walk (Starts i) (Finishes i) := (Fin.cases p (Fin.cases q (Fin.cases u (Fin.cases v (fun i ↦ Fin.elim0 i)))))
def T : TrailFamily G 4 where
  start := Starts
  finish := Finishes
  walk := Walks
  isTrail := by intro i; simp only [Walk.isTrail_def]; revert i; decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 4, i ≠ j → ∀ e : Sym2 (Fin 8),
        e ∈ (Walks i).edges → e ∉ (Walks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

abbrev goodStarts : Fin 3 → Fin 8 := ![7,3,0]
abbrev goodFinishes : Fin 3 → Fin 8 := ![3,1,5]
def goodWalks : ∀ i, G.Walk (goodStarts i) (goodFinishes i) := (Fin.cases goodP (Fin.cases goodQ (Fin.cases goodR (fun i ↦ Fin.elim0 i))))
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
    have hd : ∀ i j : Fin 3, i ≠ j → ∀ e : Sym2 (Fin 8),
        e ∈ (goodWalks i).edges → e ∉ (goodWalks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

abbrev quota : Fin 8 → ℕ := ![1,1,0,0,2,1,2,1]
lemma quota_table (v : Fin 8) : T.quota v=quota v := by
  rw [TrailFamily.quota,Nat.card_eq_fintype_card]
  revert v
  decide
lemma connected : G.Connected := by decide
lemma even_set : {v : Fin 8 | Even (Nat.card (G.neighborSet v))}=(evenVerts : Set (Fin 8)) := by
  ext v
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Set.mem_setOf_eq,Finset.mem_coe]
  revert v
  decide
lemma even_independent {x y : Fin 8}
    (hx : Even (Nat.card (G.neighborSet x))) (hy : Even (Nat.card (G.neighborSet y))) : ¬G.Adj x y := by
  have hx' : x ∈ evenVerts := by
    change x ∈ ({v : Fin 8 | Even (Nat.card (G.neighborSet v))}) at hx
    rwa [even_set] at hx
  have hy' : y ∈ evenVerts := by
    change y ∈ ({v : Fin 8 | Even (Nat.card (G.neighborSet v))}) at hy
    rwa [even_set] at hy
  have hh : ∀ x ∈ evenVerts, ∀ y ∈ evenVerts, ¬G.Adj x y := by decide
  exact hh x hx' y hy'
lemma exact_budget : (4 : ℕ)=⌈(Fintype.card (Fin 8) : ℚ)/2⌉₊ := by norm_num
lemma edge_card : G.edgeSet.ncard=9 := by
  rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,←edgeFinset_card]
  decide
lemma one_defect : T.score+1=G.edgeSet.ncard+4 := by
  rw [edge_card]
  simp [TrailFamily.score,T,Walks,p,q,u,v,Fin.sum_univ_succ,Walk.verts_toSubgraph]
  simp only [Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
  decide
lemma rooted : HasRoot T 0 := by
  let h : G.Adj 0 2 := by decide
  let Q : G.Walk 2 6 := .cons (by decide : G.Adj 2 1)
    (.cons (by decide : G.Adj 1 3) (.cons (by decide : G.Adj 3 0) (.cons (by decide : G.Adj 0 6) .nil)))
  exact hasRoot_of_rep T 0 rfl rfl h Q rfl (by simp only [Walk.isTrail_def]; decide) (by decide)
lemma root_quota_one : T.quota 0=1 := by rw [quota_table]; rfl
lemma no_nil : ∀ i, ¬(T.walk i).Nil := by decide
lemma quota_le_two (v : Fin 8) : T.quota v ≤ 2 := by rw [quota_table]; revert v; decide
lemma boundary : (boundaryGraph G (outside : Set (Fin 8))).edgeSet={s(0,4),s(0,6)} := by
  have he (p q : Prop) : p ≠ q ↔ ¬(p ↔ q) :=
    ⟨fun h hi ↦ h (propext hi),fun h hi ↦ h (hi ▸ Iff.rfl)⟩
  ext e
  induction e using Sym2.ind with
  | h a b =>
    change (G.Adj a b ∧ ((a ∈ outside) ≠ (b ∈ outside))) ↔
      s(a,b) ∈ ({s(0,4),s(0,6)} : Set (Sym2 (Fin 8)))
    rw [he]
    revert a b
    decide
lemma no_paths_with_same_quotas :
    ¬∃ U : TrailFamily G 4, (∀ v, U.quota v=T.quota v) ∧ ∀ i, (U.walk i).IsPath := by
  rintro ⟨U,hq,hp⟩
  have hh := path_family_cut_bound U hp outside 0 (by decide)
  simp_rw [hq,quota_table] at hh
  have hd : Nat.card (G.neighborSet 0)=5 := by rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]; decide
  have hc : ∑ v ∈ outside, quota v=6 := by decide
  have hb : ({s(0,4),s(0,6)} : Set (Sym2 (Fin 8))).ncard=2 := by
    rw [Set.ncard_pair (by decide)]
  rw [hd,hc,boundary,hb] at hh
  norm_num [quota] at hh
lemma constrained_maximum (U : TrailFamily G 4) (hq : ∀ v, U.quota v=T.quota v) : U.score ≤ T.score := by
  have hb := U.score_le_edges_add
  have hn : U.score ≠ G.edgeSet.ncard+4 := by
    intro hh
    exact no_paths_with_same_quotas ⟨U,hq,U.score_eq_edges_add_iff.mp hh⟩
  have ht := one_defect
  omega
lemma good_paths : ∀ i, (U.walk i).IsPath := by simp only [Walk.isPath_def]; decide
lemma graph_has_three_paths : ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ 3 :=
  MatchingAppend.path_family_partition U good_paths

end Erdos583IndependentRootObstructionDevelopment
