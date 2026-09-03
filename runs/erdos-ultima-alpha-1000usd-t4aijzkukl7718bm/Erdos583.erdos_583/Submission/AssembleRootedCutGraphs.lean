import Submission.Work

/-! Assembly of a rooted cut across a graph extension. Coverage and all cross
edge-disjointness hypotheses are explicit. -/
namespace Erdos583AssembleRootedCutGraphsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted
open Erdos583Work.RootedTailSystem
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma assemble_cut_graphs {V : Type*} {H G : SimpleGraph V} {k : ℕ}
    (hHG : H ≤ G)
    (T : TrailFamily H k) (r : V) (A : Finset (Fin k))
    (α : Fin k × Bool → V) (hfix : ∀ s, s.1 ∉ A → α s=T.endpoint s)
    (q : ∀ s : {s : Fin k × Bool // s.1 ∈ A}, G.Walk (α s.val) r)
    (hq : ∀ s, (q s).IsTrail)
    (hqq : Pairwise fun s t ↦ Disjoint (q s).toSubgraph.edgeSet (q t).toSubgraph.edgeSet)
    (hcross : ∀ s i, i ∉ A → Disjoint (q s).toSubgraph.edgeSet (T.walk i).toSubgraph.edgeSet)
    (hU : ∀ e, e ∈ G.edgeSet ↔
      (∃ s, e ∈ (q s).toSubgraph.edgeSet) ∨ ∃ i, i ∉ A ∧ e ∈ (T.walk i).toSubgraph.edgeSet)
    (hout : ∀ i, i ∉ A → r ∉ (T.walk i).support) :
    ∃ S : TrailFamily G k, (∀ s, S.endpoint s=α s) ∧
      ∃ Q : RootedCut S r A,
        (∀ s, (Q.tail s).toSubgraph=(q s).toSubgraph) ∧
        (∀ i, i ∉ A → (S.walk i).toSubgraph=((T.walk i).mapLe hHG).toSubgraph) := by
  classical
  let a (i : Fin k) := α (i,true)
  let b (i : Fin k) := α (i,false)
  have hp (i : Fin k) : ∃ p : G.Walk (a i) (b i), p.IsTrail ∧
      (∀ hi : i ∈ A, p.toSubgraph = (q ⟨(i,true),hi⟩).toSubgraph ⊔
        (q ⟨(i,false),hi⟩).toSubgraph) ∧
      (i ∉ A → p.toSubgraph = ((T.walk i).mapLe hHG).toSubgraph) := by
    by_cases hi : i ∈ A
    · refine ⟨(q ⟨(i,true),hi⟩).append (q ⟨(i,false),hi⟩).reverse, ?_, ?_, ?_⟩
      · exact trail_append_of_disjoint (hq _) (hq _).reverse (by
          simpa using hqq (show (⟨(i,true),hi⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠
            ⟨(i,false),hi⟩ by intro h; have := congrArg (fun s ↦ s.val.2) h; contradiction))
      · intro _; simp
      · exact fun hn ↦ (hn hi).elim
    · have ha : a i = T.start i := by simp only [a,hfix (i,true) hi,TrailFamily.endpoint]; rfl
      have hb : b i = T.finish i := by simp only [b,hfix (i,false) hi,TrailFamily.endpoint]; rfl
      exact ⟨((T.walk i).mapLe hHG).copy ha.symm hb.symm, by simpa using (T.isTrail i).mapLe hHG,
        fun hh ↦ (hi hh).elim, fun _ ↦ NormalTrailSystem.walk_copy_subgraph _ _ _⟩
  choose p hp hpA hpO using hp
  have hcross' (s : {s : Fin k × Bool // s.1 ∈ A}) (i : Fin k) (hi : i ∉ A) :
      Disjoint (q s).toSubgraph.edgeSet (p i).toSubgraph.edgeSet := by
    rw [hpO i hi]
    simpa [Walk.mapLe] using hcross s i hi
  have hdis : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet := by
    intro i j hij
    by_cases hi : i ∈ A
    · rw [hpA i hi,Subgraph.edgeSet_sup]
      by_cases hj : j ∈ A
      · rw [hpA j hj,Subgraph.edgeSet_sup]
        apply disjoint_sup_left.mpr
        constructor <;> apply disjoint_sup_right.mpr
        all_goals
          constructor <;> apply hqq <;>
            intro hh <;> exact hij (congrArg (fun s ↦ s.val.1) hh)
      · exact disjoint_sup_left.mpr ⟨hcross' _ j hj,(hcross' _ j hj)⟩
    · by_cases hj : j ∈ A
      · rw [hpA j hj,Subgraph.edgeSet_sup]
        exact disjoint_sup_right.mpr ⟨(hcross' _ i hi).symm,(hcross' _ i hi).symm⟩
      · rw [hpO i hi,hpO j hj]; simpa [Walk.mapLe] using T.disjoint hij
  have hqmember (s : {s : Fin k × Bool // s.1 ∈ A}) :
      (q s).toSubgraph ≤ (p s.val.1).toSubgraph := by
    rw [hpA _ s.property]
    rcases s with ⟨⟨i,c⟩,hi⟩
    cases c
    · exact le_sup_right
    · exact le_sup_left
  have hcov : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (p i).toSubgraph.edgeSet := by
    intro e
    constructor
    · intro he
      rcases (hU e).mp he with ⟨s,hs⟩|⟨i,hi,hei⟩
      · exact ⟨s.val.1,Subgraph.edgeSet_mono (hqmember s) hs⟩
      · refine ⟨i,?_⟩
        rw [hpO i hi]
        simpa [Walk.mapLe] using hei
    · rintro ⟨i,hi⟩
      exact (p i).toSubgraph.edgeSet_subset hi
  let S : TrailFamily G k := ⟨a,b,p,hp,hdis,hcov⟩
  have hends (s : Fin k × Bool) : S.endpoint s = α s := by
    rcases s with ⟨i,c⟩
    cases c <;> rfl
  let q' (s : {s : Fin k × Bool // s.1 ∈ A}) : G.Walk (S.endpoint s.val) r :=
    (q s).copy (hends s.val).symm rfl
  have hq'e (s) : (q' s).toSubgraph = (q s).toSubgraph :=
    NormalTrailSystem.walk_copy_subgraph _ _ _
  let Q : RootedCut S r A :=
    { tail := q',
      trail := fun s ↦ by simpa only [q',Walk.isTrail_copy] using hq s,
      disjoint := by intro s t hst; rw [hq'e,hq'e]; exact hqq hst,
      decomp := by intro i hi; rw [hq'e,hq'e]; exact hpA i hi,
      outside := by
        intro i hi
        rw [← Walk.mem_verts_toSubgraph]
        change r ∉ (p i).toSubgraph.verts
        rw [hpO i hi,Walk.mem_verts_toSubgraph,Walk.support_mapLe_eq_support]
        exact hout i hi }
  exact ⟨S,hends,Q,hq'e,hpO⟩

end Erdos583AssembleRootedCutGraphsDevelopment
