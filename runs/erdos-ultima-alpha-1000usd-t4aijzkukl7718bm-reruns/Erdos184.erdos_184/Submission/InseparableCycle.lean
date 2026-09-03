import Submission.WeakFanPaths
import Submission.EndpointFanAugmentation
import Submission.EndpointSeparation

/-!
Cyclability of an inseparable target set. Vertices outside that set need
not retain positive degree or participate in the connectivity hypotheses.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InseparableCycle
open CyclicModel CycleAugmentation
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

/-- Reachability from the new vertex to surviving old targets is enough.
If there is no larger fan, the only possible small separator is precisely
all the old targets, and a fan ending at those targets also gives a clean arc. -/
lemma augment_of_target_connectivity {n : ℕ} (M : Model G n) {a : V}
    (ha : a ∉ Set.range M.vertex) (T : Set V) (hT : T ⊆ Set.range M.vertex)
    (hsize : 2 ≤ T.ncard)
    (hconn : ∀ S : Set V, S.ncard ≤ T.ncard → (haS : a ∉ S) →
      ∀ b ∈ T, ∀ hbS : b ∉ S, (G.induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      a ∈ H.verts ∧ T ⊆ H.verts := by
  by_cases hf : ∀ S : Set V, S.ncard < T.ncard+1 → (haS : a ∉ S) →
      ∃ b ∈ Set.range M.vertex, ∃ hbS : b ∉ S,
        (G.induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩
  · obtain ⟨w,p,hwi,hw,hp,hi,hfirst⟩ := FanPaths.fan_of_reaches_set
      (Set.range M.vertex) ha (T.ncard+1) hf
    exact augment_with_endpoint_fan M T hT (by omega) w p hwi hw hp hi
      ((Set.ncard_le_ncard Set.diff_subset).trans_lt (by omega)) hfirst
  · push_neg at hf
    obtain ⟨S,hS,haS,hno⟩ := hf
    have hTS : T ⊆ S := by
      intro b hb
      by_contra hbS
      exact hno b (hT hb) hbS (hconn S (by omega) haS b hb hbS)
    have heq : T = S := Set.eq_of_subset_of_ncard_le hTS (by omega)
    subst S
    have hweak : ∀ S : Set V, S.ncard < T.ncard → (haS : a ∉ S) →
        ∃ b ∈ Set.range M.vertex, ∃ hbS : b ∉ S,
          (G.induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩ := by
      intro S hS haS
      have hn : ¬T ⊆ S := by
        intro hs
        have hh := Set.ncard_le_ncard hs
        omega
      obtain ⟨b,hb,hbS⟩ := Set.not_subset.mp hn
      exact ⟨b,hT hb,hbS,hconn S (by omega) haS b hb hbS⟩
    obtain ⟨w,p,hwi,hw,hp,hi,hfirst⟩ := FanPaths.fan_of_reaches_set
      (Set.range M.vertex) ha T.ncard hweak
    have hwT : Set.range w ⊆ T := by
      rintro b ⟨i,rfl⟩
      by_contra hbT
      have hs : ∀ x, x ∈ (p i).support → x ∈ Tᶜ := by
        intro x hx hxT
        exact hbT ((hfirst i x hx (hT hxT)) ▸ hxT)
      exact hno (w i) (hw i) hbT ⟨(p i).induce Tᶜ hs⟩
    have heq : Set.range w = T := Set.eq_of_subset_of_ncard_le hwT (by
      rw [Set.ncard_range_of_injective hwi,Nat.card_fin])
    apply augment_with_endpoint_fan M T hT hsize w p hwi hw hp hi _ hfirst
    rw [heq,Set.diff_self,Set.ncard_empty]
    omega

/-- In an even graph, an at-least-two-vertex set with no separator smaller
than its own cardinality lies on a common simple cycle. -/
lemma cycle_through_inseparable_set (he : ∀ x, Even (G.degree x))
    (T : Set V) (hT : 2 ≤ T.ncard)
    (hconn : ∀ S : Set V, S.ncard < T.ncard →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        (G.induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ T ⊆ H.verts := by
  obtain ⟨a,b,ha,hb,hab⟩ := (Set.one_lt_ncard_iff (s := T)).mp (by omega)
  obtain ⟨H₀,hH₀,ha₀,hb₀⟩ := EndpointSeparation.cycle_through_pair_of_even he hab
    (fun S hS haS hbS => hconn S (by omega) a ha b hb haS hbS)
  let D := Finset.univ.filter (fun H : G.Subgraph =>
    (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ a ∈ H.verts ∧ b ∈ H.verts)
  have hD : D.Nonempty := ⟨H₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH₀,ha₀,hb₀⟩⟩
  obtain ⟨H,hH,hmax⟩ := Finset.exists_max_image D (fun H => (T ∩ H.verts).ncard) hD
  obtain ⟨hcH,haH,hbH⟩ := (Finset.mem_filter.mp hH).2
  refine ⟨H,hcH,?_⟩
  by_contra hn
  obtain ⟨c,hcT,hcH'⟩ := Set.not_subset.mp hn
  obtain ⟨p,hp,hpH⟩ := CycleRing.cycle_piece_walk_at H hcH.1 hcH.2 a haH
  obtain ⟨n,M,hM⟩ := model_of_cycle p hp
  rw [hpH] at hM
  have hlow : 2 ≤ (T ∩ H.verts).ncard := by
    have hh := (Set.one_lt_ncard_iff (s := T ∩ H.verts)).mpr ⟨a,b,⟨ha,haH⟩,⟨hb,hbH⟩,hab⟩
    omega
  have hsize : (T ∩ H.verts).ncard < T.ncard :=
    Set.ncard_lt_ncard ⟨Set.inter_subset_left,fun hs => hcH' (hs hcT).2⟩
  obtain ⟨J,hJ,hcJ,hTJ⟩ := augment_of_target_connectivity M (by rwa [hM]) (T ∩ H.verts)
    (by rw [hM]; exact Set.inter_subset_right) hlow (by
      intro S hS hcS d hd hdS
      exact hconn S (by omega) c hcT d hd.1 hcS hdS)
  have hsub : T ∩ H.verts ⊂ T ∩ J.verts := by
    refine ⟨fun _ hx => ⟨hx.1,hTJ hx⟩,?_⟩
    intro hs
    exact hcH' (hs ⟨hcT,hcJ⟩).2
  have hh := hmax J (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hJ,hTJ ⟨ha,haH⟩,hTJ ⟨hb,hbH⟩⟩)
  exact (not_lt_of_ge hh) (Set.ncard_lt_ncard hsub)

end Erdos184.InseparableCycle
