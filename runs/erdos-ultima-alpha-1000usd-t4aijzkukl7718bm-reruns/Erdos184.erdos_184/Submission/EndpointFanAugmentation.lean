import Submission.CycleAugmentation

/-! Clean-arc augmentation when the fan endpoints cover the retained targets. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleAugmentation
open CyclicModel CyclicSegments
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

lemma augment_with_endpoint_fan {n k : ℕ} (M : Model G n) {a : V}
    (T : Set V) (hT : T ⊆ Set.range M.vertex) (hk : 2 ≤ k)
    (w : Fin k → V) (p : ∀ i, G.Walk a (w i))
    (hwi : Function.Injective w) (hw : ∀ i, w i ∈ Set.range M.vertex)
    (hp : ∀ i, (p i).IsPath)
    (hmeet : ∀ i j, i ≠ j → ∀ x, x ∈ (p i).support → x ∈ (p j).support → x = a)
    (hsize : (T \ Set.range w).ncard < k)
    (hfirst : ∀ i x, x ∈ (p i).support → x ∈ Set.range M.vertex → x = w i) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      a ∈ H.verts ∧ T ⊆ H.verts := by
  choose e he using hw
  have hei : Function.Injective e := by
    intro i j hij
    apply hwi
    rw [← he i,← he j,hij]
  let R : Set (Fin (n+3)) := Set.range e
  let U : Set (Fin (n+3)) := M.vertex ⁻¹' T
  have hR : R.ncard = k := by
    rw [Set.ncard_range_of_injective hei,Nat.card_fin]
  have hU : (U \ R).ncard ≤ (T \ Set.range w).ncard := by
    apply Set.ncard_le_ncard_of_injOn M.vertex _ M.injective.injOn
    intro x hx
    refine ⟨hx.1,?_⟩
    rintro ⟨i,hi⟩
    exact hx.2 ⟨i,M.injective ((he i).trans hi)⟩
  have hcard : (U \ R).ncard < R.ncard := by omega
  let f := finRotate (n+3)
  let seg : ∀ b : R, Segment f R b := fun b => Classical.choice (exists_segment f R b)
  obtain ⟨b,hclean⟩ := exists_clean_segment f R U seg hcard
  have hother : ∃ c : R, c ≠ b := by
    obtain ⟨x,y,hx,hy,hxy⟩ := (Set.one_lt_ncard_iff (s := R)).mp (show 1 < R.ncard from by omega)
    by_cases hxb : x = b.val
    · exact ⟨⟨y,hy⟩,fun h => hxy (hxb.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨x,hx⟩,fun h => hxb (congrArg Subtype.val h)⟩
  have hend := last_ne_start f (seg b) rotation_transitive hother
  have hlen := length_lt_card f (seg b) hend
  simp only [Fintype.card_fin] at hlen
  obtain ⟨r,hr,hrS,hrT⟩ := complementary_path M b.val (seg b).length (seg b).pos hlen T hT hclean
  obtain ⟨i,hi⟩ := b.property
  obtain ⟨j,hj⟩ := (seg b).last
  have hij : i ≠ j := by
    intro h
    exact hend (hj.symm.trans ((congrArg e h).symm.trans hi))
  let P : G.Walk a (M.vertex b.val) := (p i).copy rfl ((he i).symm.trans (congrArg M.vertex hi))
  let Q : G.Walk a (M.vertex ((f : Fin (n+3) → Fin (n+3))^[(seg b).length] b.val)) :=
    (p j).copy rfl ((he j).symm.trans (congrArg M.vertex hj))
  have hPQ : ∀ x, x ∈ P.support → x ∈ Q.support → x = a := by
    intro x hx hy
    exact hmeet i j hij x (by simpa only [P,Walk.support_copy] using hx)
      (by simpa only [Q,Walk.support_copy] using hy)
  have hPS : ∀ x, x ∈ P.support → x ∈ Set.range M.vertex → x = M.vertex b.val := by
    intro x hx hy
    exact (hfirst i x (by simpa only [P,Walk.support_copy] using hx) hy).trans
      ((he i).symm.trans (congrArg M.vertex hi))
  have hQS : ∀ x, x ∈ Q.support → x ∈ Set.range M.vertex →
      x = M.vertex ((f : Fin (n+3) → Fin (n+3))^[(seg b).length] b.val) := by
    intro x hx hy
    exact (hfirst j x (by simpa only [Q,Walk.support_copy] using hx) hy).trans
      ((he j).symm.trans (congrArg M.vertex hj))
  have hcycle := join_fan (Set.range M.vertex) P Q r
    ((Walk.isPath_copy _ _ _).mpr (hp i)) ((Walk.isPath_copy _ _ _).mpr (hp j)) hr
    (fun h => hend (M.injective h.symm)) hPQ hPS hQS hrS
  let c := (P.reverse.append Q).append r
  refine ⟨c.toSubgraph,cycle_subgraph_regular G hcycle,?_,?_⟩
  · apply c.mem_verts_toSubgraph.mpr
    exact Walk.subset_support_append_left _ _
      (Walk.subset_support_append_right _ _ Q.start_mem_support)
  · intro x hx
    exact c.mem_verts_toSubgraph.mpr (Walk.subset_support_append_right _ _ (hrT x hx))

end Erdos184.CycleAugmentation
