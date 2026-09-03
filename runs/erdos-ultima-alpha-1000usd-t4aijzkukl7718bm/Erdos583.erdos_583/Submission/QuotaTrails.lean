import Submission.DistinctTails

/-! Indexed trail families with endpoint quotas, allowing repeated endpoint
labels and nil members. This development does not assert normalization. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583DistinctTailsDevelopment
namespace Erdos583QuotaTrailsDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

structure TrailFamily {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  start : Fin k → V
  finish : Fin k → V
  walk : ∀ i, G.Walk (start i) (finish i)
  isTrail : ∀ i, (walk i).IsTrail
  disjoint : Pairwise fun i j ↦ Disjoint (walk i).toSubgraph.edgeSet (walk j).toSubgraph.edgeSet
  cover : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (walk i).toSubgraph.edgeSet

namespace TrailFamily

def endpoint {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (x : Fin k × Bool) : V :=
  if x.2 then T.start x.1 else T.finish x.1

noncomputable def quota {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (v : V) : ℕ :=
  Nat.card {x : Fin k × Bool // T.endpoint x = v}

lemma quota_eq_of_endpoint_perm {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (S T : TrailFamily G k) (e : Equiv.Perm (Fin k × Bool))
    (he : ∀ x, S.endpoint x = T.endpoint (e x)) (v : V) : S.quota v = T.quota v := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv e (fun x ↦ by rw [he x])

lemma endpoint_mem_support {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (x : Fin k × Bool) : T.endpoint x ∈ (T.walk x.1).support := by
  rcases x with ⟨i,b⟩
  cases b <;> simp [endpoint]

/-- Total distinct vertex incidences among the trails. -/
noncomputable def score {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : ℕ :=
  ∑ i, (T.walk i).toSubgraph.verts.ncard

lemma score_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : T.score ≤ k * Fintype.card V := by
  unfold score
  calc
    ∑ i, (T.walk i).toSubgraph.verts.ncard ≤ ∑ _i : Fin k, Fintype.card V := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (T.walk i).toSubgraph.verts
    _ = _ := by simp

/-- The global incidence optimization has a maximum. This does not assert
that a maximizing system consists of simple paths. -/
lemma exists_max_score {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) :
    ∃ S : TrailFamily G k, ∀ R : TrailFamily G k, R.score ≤ S.score := by
  classical
  let P (m : ℕ) := ∃ S : TrailFamily G k, S.score = m
  have hm : P (Nat.findGreatest P (k * Fintype.card V)) :=
    Nat.findGreatest_spec T.score_le ⟨T, rfl⟩
  obtain ⟨S, hS⟩ := hm
  refine ⟨S, fun R ↦ ?_⟩
  rw [hS]
  exact Nat.le_findGreatest R.score_le ⟨R, rfl⟩

lemma sum_length {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : ∑ i, (T.walk i).length = G.edgeSet.ncard := by
  classical
  let E (i : Fin k) : Finset (Sym2 V) := (T.walk i).edges.toFinset
  have hE : Finset.univ.biUnion E = G.edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_edgeFinset]
    simpa only [E, List.mem_toFinset, Walk.mem_edges_toSubgraph] using (T.cover e).symm
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) E := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact Set.disjoint_left.mp (T.disjoint hij)
      ((T.walk i).mem_edges_toSubgraph.mpr (List.mem_toFinset.mp hi))
      ((T.walk j).mem_edges_toSubgraph.mpr (List.mem_toFinset.mp hj))
  have hcard (i : Fin k) : (E i).card = (T.walk i).length := by
    change (T.walk i).edges.toFinset.card = (T.walk i).length
    rw [List.toFinset_card_of_nodup (T.isTrail i).edges_nodup, Walk.length_edges]
  calc
    ∑ i, (T.walk i).length = ∑ i, (E i).card := by simp only [hcard]
    _ = (Finset.univ.biUnion E).card := (Finset.card_biUnion hdis).symm
    _ = G.edgeSet.ncard := by rw [hE, ← Set.ncard_coe_finset, coe_edgeFinset]

lemma vertex_incidence_le {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) :
    (T.walk i).toSubgraph.verts.ncard ≤ (T.walk i).length + 1 := by
  classical
  rw [Walk.verts_toSubgraph, ← List.coe_toFinset, Set.ncard_coe_finset]
  simpa only [Walk.length_support] using (T.walk i).support.toFinset_card_le

lemma vertex_incidence_eq_iff {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) :
    (T.walk i).toSubgraph.verts.ncard = (T.walk i).length + 1 ↔ (T.walk i).IsPath := by
  classical
  rw [Walk.verts_toSubgraph, ← List.coe_toFinset, Set.ncard_coe_finset, ← Walk.length_support]
  simpa only [List.toFinset_coe, Multiset.coe_card, Multiset.coe_nodup, Walk.isPath_def] using
    (Multiset.toFinset_card_eq_card_iff_nodup (m := ((T.walk i).support : Multiset V)))

lemma score_le_edges_add {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : T.score ≤ G.edgeSet.ncard + k := by
  calc
    T.score ≤ ∑ i, ((T.walk i).length + 1) :=
      Finset.sum_le_sum (fun i _ ↦ T.vertex_incidence_le i)
    _ = _ := by rw [Finset.sum_add_distrib, T.sum_length]; simp

/-- The deficit in total distinct vertex incidences is exactly the obstruction
to this particular normal trail system being a simple-path system. -/
lemma score_eq_edges_add_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : T.score = G.edgeSet.ncard + k ↔
      ∀ i, (T.walk i).IsPath := by
  have he : G.edgeSet.ncard + k = ∑ i, ((T.walk i).length + 1) := by
    rw [Finset.sum_add_distrib, T.sum_length]; simp
  rw [he, score, Finset.sum_eq_sum_iff_of_le (fun i _ ↦ T.vertex_incidence_le i)]
  simp only [Finset.mem_univ, true_implies, T.vertex_incidence_eq_iff]

noncomputable def defect {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) : ℕ :=
  (T.walk i).length + 1 - (T.walk i).toSubgraph.verts.ncard

lemma defect_add_vertices {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) :
    T.defect i + (T.walk i).toSubgraph.verts.ncard = (T.walk i).length + 1 :=
  Nat.sub_add_cancel (T.vertex_incidence_le i)

lemma defect_eq_zero_iff {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) : T.defect i = 0 ↔ (T.walk i).IsPath := by
  rw [← T.vertex_incidence_eq_iff i]
  have h := T.defect_add_vertices i
  omega

lemma sum_defect_add_score {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) : (∑ i, T.defect i) + T.score = G.edgeSet.ncard + k := by
  change (∑ i, T.defect i) + (∑ i, (T.walk i).toSubgraph.verts.ncard) = _
  rw [← Finset.sum_add_distrib]
  simp only [T.defect_add_vertices]
  rw [Finset.sum_add_distrib, T.sum_length]
  simp

lemma one_defect_other_paths {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hscore : T.score + 1 = G.edgeSet.ncard + k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) :
    T.defect i = 1 ∧ ∀ j, j ≠ i → (T.walk j).IsPath := by
  classical
  have hs : ∑ j, T.defect j = 1 := by have := T.sum_defect_add_score; omega
  have hp : 0 < T.defect i := Nat.pos_of_ne_zero (fun hz ↦ hi ((T.defect_eq_zero_iff i).mp hz))
  have he := Finset.sum_erase_add (s := Finset.univ) (f := T.defect) (Finset.mem_univ i)
  have hz : ∑ j ∈ Finset.univ.erase i, T.defect j = 0 := by omega
  have hone : T.defect i = 1 := by omega
  refine ⟨hone, fun j hji ↦ (T.defect_eq_zero_iff j).mp ?_⟩
  have hle : T.defect j ≤ ∑ l ∈ Finset.univ.erase i, T.defect l :=
    Finset.single_le_sum (fun l _ ↦ Nat.zero_le _) (by simp [hji])
  omega

end TrailFamily
end Erdos583QuotaTrailsDevelopment
