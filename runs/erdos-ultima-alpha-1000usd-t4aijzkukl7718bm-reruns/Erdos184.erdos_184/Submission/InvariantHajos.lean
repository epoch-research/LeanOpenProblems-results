import Submission.InvariantLowDegree
import Submission.WeightedPaths

/-!
A path rotation supplies a cycle through two degree-two vertices in the
hereditary two-vertex-intersection class. This is not a theorem about arbitrary
count-critical graphs.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.InvariantPartitions
variable {V : Type*} [Fintype V]

lemma exists_cycle_two_degree_two (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥)
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2) :
    ∃ C : G.Subgraph, (C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) ∧
      ∃ u w : V, u ≠ w ∧ u ∈ C.verts ∧ w ∈ C.verts ∧
        G.degree u = 2 ∧ G.degree w = 2 := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  letI : Nonempty V := ⟨a⟩
  obtain ⟨u,v,p,hp,hm⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hu := longest_path_start_degree_two_of_intersection_le_two G he hne hi p hp hm
  have hN : (G.neighborSet u).ncard = 2 := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hu
  obtain ⟨x,hx,hx1⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < (G.neighborSet u).ncard by omega)
    (p.getVert 1)
  have hxs := longest_path_start_neighbors p hp hm x hx
  obtain ⟨i,hix,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hxs
  have hi2 : 2 ≤ i := by
    by_contra h
    have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl
    · have hxu : u = x := by simpa using hix
      exact (G.ne_of_adj hx) hxu
    · exact hx1 hix.symm
  let j := i-1
  have hji : j+1 = i := by omega
  have hj : j < p.length := by omega
  have haux : G.Adj u (p.getVert (j+1)) := by simpa only [hji,hix] using hx
  let r := (p.take j).reverse.append ((p.drop (j+1)).cons haux)
  have hr : r.IsPath := WeightedPaths.rotate_isPath (p.take j) (p.drop (j+1))
    (p.adj_getVert_succ hj) haux (by rwa [WeightedPaths.take_cons_drop p j hj])
  have hrl : r.length = p.length := by
    have hh := congrArg Walk.length (WeightedPaths.take_cons_drop p j hj)
    simpa only [r,Walk.length_append,Walk.length_reverse,Walk.length_cons] using hh
  have hw : G.degree (p.getVert j) = 2 :=
    longest_path_start_degree_two_of_intersection_le_two G he hne hi r hr (by
      intro a b q hq
      rw [hrl]
      exact hm a b q hq)
  have huw : u ≠ p.getVert j := by
    intro h
    have hh := hp.getVert_injOn (show 0 ≤ p.length by omega) (show j ≤ p.length by omega)
      (by simpa using h)
    omega
  have hux : G.Adj (p.getVert i) u := by simpa only [hix] using hx.symm
  let c := (p.take i).cons hux
  have hc : c.IsCycle := path_close_isCycle (p.take i) (Walk.IsPath.of_append_left (q := p.drop i) (by rwa [Walk.append_take_drop_eq]))
    (by simpa only [Walk.take_length,min_eq_left hil] using hi2) hux
  refine ⟨c.toSubgraph,cycle_subgraph_regular G hc,u,p.getVert j,huw,?_,?_,hu,hw⟩
  · apply c.mem_verts_toSubgraph.mpr
    simp only [c,Walk.support_cons,List.mem_cons]
    exact Or.inr (p.take i).start_mem_support
  · apply c.mem_verts_toSubgraph.mpr
    simp only [c,Walk.support_cons,List.mem_cons]
    apply Or.inr
    have hh := (p.take i).getVert_mem_support j
    simpa only [Walk.take_getVert, min_eq_right (show j ≤ i by omega)] using hh

lemma cycle_delete_unsupported_degree_two {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (v : V)
    (hv : v ∈ C.verts) (hd : G.degree v = 2) : v ∉ (G \ C.spanningCoe).support := by
  have hcd : C.spanningCoe.degree v = 2 := by
    have hh := hc.2 ⟨v,hv⟩
    rw [Subgraph.coe_degree] at hh
    rw [Subgraph.degree_spanningCoe]
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
  apply ((G \ C.spanningCoe).degree_eq_zero_iff_notMem_support v).mp
  have hh := degree_sdiff_of_le C.spanningCoe_le v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hd hcd ⊢
  omega

lemma cycle_two_degree_two_support_loss {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (u w : V) (huw : u ≠ w)
    (hu : u ∈ C.verts) (hw : w ∈ C.verts) (hdu : G.degree u = 2) (hdw : G.degree w = 2) :
    (G \ C.spanningCoe).support.ncard + 2 ≤ G.support.ncard := by
  have hnu := cycle_delete_unsupported_degree_two C hc u hu hdu
  have hnw := cycle_delete_unsupported_degree_two C hc w hw hdw
  have hsu : u ∈ G.support := (G.degree_pos_iff_mem_support u).mp (by omega)
  have hsw : w ∈ G.support := (G.degree_pos_iff_mem_support w).mp (by omega)
  have hsub : ({u,w} : Set V) ⊆ G.support \ (G \ C.spanningCoe).support := by
    intro v hv
    rcases (Set.mem_insert_iff.mp hv) with rfl | hv
    · exact ⟨hsu,hnu⟩
    · have hv' : v = w := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨hsw,hnw⟩
  have htwo := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair huw] at htwo
  have heq := Set.ncard_diff_add_ncard_of_subset
    (SimpleGraph.support_mono (show G \ C.spanningCoe ≤ G from sdiff_le))
  omega

/-- A Hajós-type bound for the hereditary intersection-restricted class, not
for arbitrary even graphs. -/
lemma hajos_bound_of_intersection_le_two (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v))
    (hi : ∀ H K : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) →
      Disjoint H.edgeSet K.edgeSet → (H.verts ∩ K.verts).ncard ≤ 2)
    (hne : G ≠ ⊥) :
    2 * CycleNumberSubmodularity.cycleNumber G + 1 ≤ G.support.ncard := by
  generalize hn : G.support.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    obtain ⟨C,hc,u,w,huw,hu,hw,hdu,hdw⟩ := exists_cycle_two_degree_two G he hne hi
    have hdrop := cycle_two_degree_two_support_loss C hc u w huw hu hw hdu hdw
    have hlt : (G \ C.spanningCoe).support.ncard < n := by omega
    have hstep := CountCritical.number_le_residual_add_one he C hc
    by_cases hbot : G \ C.spanningCoe = ⊥
    · rw [hbot,CountCritical.number_bot] at hstep
      have hthree := cycle_edgeSet_three_le C hc.1 hc.2
      rw [regular_two_edge_vertex_card C hc.2] at hthree
      have hsub : C.verts ⊆ G.support := by
        intro v hv
        have hdC := hc.2 ⟨v,hv⟩
        have hpos : 0 < C.coe.degree ⟨v,hv⟩ := by
          simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdC ⊢
          omega
        obtain ⟨z,hz⟩ := (C.coe.degree_pos_iff_exists_adj ⟨v,hv⟩).mp hpos
        exact ⟨z.val,C.adj_sub hz⟩
      have hh := Set.ncard_le_ncard hsub
      omega
    · have heR := CountCritical.residual_even he C hc
      have hR := ih _ hlt (G \ C.spanningCoe) (by
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR v)
        (intersection_le_two_of_le (A := G \ C.spanningCoe) sdiff_le hi) hbot rfl
      omega

lemma HasInvariantCount.hajos_bound {G : SimpleGraph V}
    (hi : HasInvariantCount G) (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥)
    (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : IsDecomposition G D) : 2 * D.card + 1 ≤ G.support.ncard := by
  have hb := hajos_bound_of_intersection_le_two G he (hi.intersection_le_two he) hne
  obtain ⟨E,hcE,hdE,hE⟩ := CountCritical.minimum_exists G he
  have hh := hi D E hcD hdD hcE hdE
  rw [hh,hE]
  exact hb

/-- The critical-invariance hypothesis would imply the full Hajós numerical
bound, not merely an unspecified linear bound. This premise is unproved. -/
lemma number_hajos_bound_of_critical_invariance (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥)
    (hinv : ∀ H : SimpleGraph V, H ≤ G → ∀ k,
      CountCritical.IsCountCritical k H → HasInvariantCount H) :
    2 * CycleNumberSubmodularity.cycleNumber G + 1 ≤ G.support.ncard := by
  by_cases hk : CycleNumberSubmodularity.cycleNumber G = 0
  · have hs := support_card_two_le G hne
    omega
  obtain ⟨H,hHG,hH⟩ := CountCritical.extract G he (CycleNumberSubmodularity.cycleNumber G)
    (Nat.pos_of_ne_zero hk) le_rfl
  have hHne : H ≠ ⊥ := by
    intro h
    have hh := hH.2.1
    rw [h,CountCritical.number_bot] at hh
    exact hk hh.symm
  have hb := hajos_bound_of_intersection_le_two H hH.1
    ((hinv H hHG _ hH).intersection_le_two hH.1) hHne
  rw [hH.2.1] at hb
  exact hb.trans (Set.ncard_le_ncard (SimpleGraph.support_mono hHG))

end Erdos184.InvariantPartitions
