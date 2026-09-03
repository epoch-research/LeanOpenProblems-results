import Submission.CyclicModel
import Submission.FanPaths
import Submission.CycleThroughTwo

/-! Adding one new vertex to a cycle while retaining a prescribed set of old vertices. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleAugmentation
open CyclicModel CyclicSegments
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

omit [Fintype V] in
lemma append_path {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ x, x ∈ p.support → x ∈ q.support → x = b) : (p.append q).IsPath := by
  have hb : b ∉ q.support.tail := by
    have hh := hq.support_nodup
    rw [Walk.support_eq_cons,List.nodup_cons] at hh
    exact hh.1
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append']
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro x hx hy
  exact hb ((hi x hx (List.mem_of_mem_tail hy)) ▸ hy)

omit [Fintype V] in
/-- Two fan legs and a path in the old cycle form a new cycle. -/
lemma join_fan {a b c : V} (S : Set V) (p : G.Walk a b) (q : G.Walk a c)
    (r : G.Walk c b) (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hbc : b ≠ c)
    (hpq : ∀ x, x ∈ p.support → x ∈ q.support → x = a)
    (hpS : ∀ x, x ∈ p.support → x ∈ S → x = b)
    (hqS : ∀ x, x ∈ q.support → x ∈ S → x = c)
    (hrS : ∀ x, x ∈ r.support → x ∈ S) :
    ((p.reverse.append q).append r).IsCycle := by
  have hP : (p.reverse.append q).IsPath := append_path p.reverse q hp.reverse hq (by
    intro x hx hy
    exact hpq x (by simpa only [Walk.support_reverse,List.mem_reverse] using hx) hy)
  have hdis (u : V) (w : V) (t : G.Walk u w)
      (htS : ∀ x, x ∈ t.support → x ∈ S → x = w) : t.edges.Disjoint r.edges := by
    intro e he hf
    induction e using Sym2.inductionOn with | _ x y =>
      have hx := htS x (t.fst_mem_support_of_mem_edges he) (hrS x (r.fst_mem_support_of_mem_edges hf))
      have hy := htS y (t.snd_mem_support_of_mem_edges he) (hrS y (r.snd_mem_support_of_mem_edges hf))
      exact (t.adj_of_mem_edges he).ne (hx.trans hy.symm)
  apply TwoTerminalGluing.append_isCycle_of_paths _ r hP hr hbc
  · rw [Walk.edges_append,List.disjoint_append_left,Walk.edges_reverse,List.disjoint_reverse_left]
    exact ⟨hdis a b p hpS,hdis a c q hqS⟩
  · intro x hx hy
    rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
    · exact Or.inl (hpS x (by simpa only [Walk.support_reverse,List.mem_reverse] using hx) (hrS x hy))
    · exact Or.inr (hqS x hx (hrS x hy))

/-- A fan with more endpoints than retained vertices, or with an endpoint at
 every old-cycle vertex, admits a clean replacement arc. -/
lemma augment_with_fan {n k : ℕ} (M : Model G n) {a : V}
    (T : Set V) (hT : T ⊆ Set.range M.vertex) (hk : 2 ≤ k)
    (hsize : T.ncard < k ∨ k = n+3)
    (w : Fin k → V) (p : ∀ i, G.Walk a (w i))
    (hwi : Function.Injective w) (hw : ∀ i, w i ∈ Set.range M.vertex)
    (hp : ∀ i, (p i).IsPath)
    (hmeet : ∀ i j, i ≠ j → ∀ x, x ∈ (p i).support → x ∈ (p j).support → x = a)
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
  have hU : U.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn M.vertex
    (fun _ hx => hx) M.injective.injOn
  have hcard : (U \ R).ncard < R.ncard := by
    rcases hsize with h | h
    · exact (Set.ncard_le_ncard Set.diff_subset).trans_lt (by omega)
    · have hs : Function.Surjective e := by
        exact ((Fintype.bijective_iff_injective_and_card e).mpr
          ⟨hei,by simp only [Fintype.card_fin]; exact h⟩).2
      have hRu : R = Set.univ := Set.range_eq_univ.mpr hs
      rw [hR,hRu,Set.diff_univ,Set.ncard_empty]
      omega
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
