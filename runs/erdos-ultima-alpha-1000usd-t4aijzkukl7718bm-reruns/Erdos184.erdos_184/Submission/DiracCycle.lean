import Submission.CycleAugmentation

/-! The finite cycle-through-vertices theorem, proved using a fan and a clean arc. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.DiracCycle
open CyclicModel CycleAugmentation
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

lemma augment_of_connectivity {n k : ℕ} (M : Model G n) {a : V}
    (ha : a ∉ Set.range M.vertex) (T : Set V) (hT : T ⊆ Set.range M.vertex)
    (hk : 2 ≤ k) (hsize : T.ncard < k)
    (hconn : ∀ S : Set V, S.ncard < k → ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Reachable u v) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      a ∈ H.verts ∧ T ⊆ H.verts := by
  let r := min k (n+3)
  have hr : 2 ≤ r := le_min hk (by omega)
  have hrc : r ≤ (Set.range M.vertex).ncard := by
    rw [Set.ncard_range_of_injective M.injective,Nat.card_fin]
    exact min_le_right _ _
  obtain ⟨w,p,hwi,hw,hp,hi,hf⟩ := FanPaths.fan_of_connectivity
    (Set.range M.vertex) ha r hrc (fun S hS => hconn S (hS.trans_le (min_le_left _ _)))
  apply augment_with_fan M T hT hr _ w p hwi hw hp hi hf
  by_cases h : k ≤ n+3
  · exact Or.inl (by simpa only [r,min_eq_left h] using hsize)
  · exact Or.inr (min_eq_right (by omega))

/-- In a graph with no separator of size less than k, any at-most-k set lies
on a cycle, provided the graph has an initial cycle and k is at least two. -/
lemma cycle_through_set {k : ℕ} (hk : 2 ≤ k) (T : Set V) (hT : T.ncard ≤ k)
    (hcycle : ∃ H : G.Subgraph, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hconn : ∀ S : Set V, S.ncard < k → ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Reachable u v) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ T ⊆ H.verts := by
  let D := Finset.univ.filter (fun H : G.Subgraph => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  have hD : D.Nonempty := by
    obtain ⟨H,hH⟩ := hcycle
    exact ⟨H,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH⟩⟩
  obtain ⟨H,hH,hmax⟩ := Finset.exists_max_image D (fun H => (T ∩ H.verts).ncard) hD
  have hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := (Finset.mem_filter.mp hH).2
  refine ⟨H,hcH,?_⟩
  by_contra hn
  obtain ⟨a,haT,haH⟩ := Set.not_subset.mp hn
  obtain ⟨b,hb⟩ := hcH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := CycleRing.cycle_piece_walk_at H hcH.1 hcH.2 b hb
  obtain ⟨n,M,hM⟩ := model_of_cycle p hp
  rw [hpH] at hM
  have hsize : (T ∩ H.verts).ncard < k := by
    apply (Set.ncard_lt_ncard (show T ∩ H.verts ⊂ T from ?_)).trans_le hT
    exact ⟨Set.inter_subset_left,fun hs => haH (hs haT).2⟩
  obtain ⟨J,hJ,haJ,hTJ⟩ := augment_of_connectivity M (by rwa [hM]) (T ∩ H.verts)
    (by rw [hM]; exact Set.inter_subset_right) hk hsize hconn
  have hsub : T ∩ H.verts ⊂ T ∩ J.verts := by
    refine ⟨fun _ hx => ⟨hx.1,hTJ hx⟩,?_⟩
    intro hs
    exact haH (hs ⟨haT,haJ⟩).2
  have hh := hmax J (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hJ⟩)
  exact (not_lt_of_ge hh) (Set.ncard_lt_ncard hsub)

/-- A degree-two lower bound supplies an initial cycle using two-connectivity. -/
lemma cycle_through_set_of_degree {k : ℕ} (hk : 2 ≤ k) (T : Set V) (hT : T.ncard ≤ k)
    (hdeg : ∃ a : V, 2 ≤ G.degree a)
    (hconn : ∀ S : Set V, S.ncard < k → ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Reachable u v) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ T ⊆ H.verts := by
  apply cycle_through_set hk T hT _ hconn
  obtain ⟨a,ha⟩ := hdeg
  obtain ⟨b,hab⟩ := (G.degree_pos_iff_exists_adj a).mp (by omega)
  obtain ⟨H,hH,_,_⟩ := CycleThroughTwo.cycle_through_pair hab.ne ha
    (fun S hS => hconn S (by omega))
  exact ⟨H,hH⟩

end Erdos184.DiracCycle
