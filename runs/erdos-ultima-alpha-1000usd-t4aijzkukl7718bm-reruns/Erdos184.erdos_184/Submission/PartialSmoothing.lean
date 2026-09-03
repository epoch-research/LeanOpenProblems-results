import Submission.ShiftedTwoVertexCuts
import Submission.GlobalVertexMinimal

/-! Partial smoothing at one vertex. A marked cycle avoiding that vertex
lifts without an extra piece; this is a necessary critical-graph obstruction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.PartialSmoothing
open ExactVertexSmoothing
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

/-- Keep the apex in the vertex type, and replace only two spokes. -/
def smooth (A : SimpleGraph V) (a b : V) : SimpleGraph V := A ⊔ edge a b

def unsmooth (A : SimpleGraph V) (v a b : V) : SimpleGraph V := A ⊔ edge v a ⊔ edge v b

omit [Fintype V] in
lemma smooth_edges (A : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    (smooth A a b).edgeSet = insert s(a,b) A.edgeSet := by
  simp only [smooth,edgeSet_sup,edge_edgeSet_of_ne hab,Set.union_singleton]

omit [Fintype V] in
lemma unsmooth_edges (A : SimpleGraph V) {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) :
    (unsmooth A v a b).edgeSet = insert s(v,b) (insert s(v,a) A.edgeSet) := by
  simp only [unsmooth,edgeSet_sup,edge_edgeSet_of_ne hva,edge_edgeSet_of_ne hvb,Set.union_singleton]

omit [Fintype V] in
lemma unsmooth_left (A : SimpleGraph V) {v a b : V} (hva : v ≠ a) :
    (unsmooth A v a b).Adj v a := Or.inl (Or.inr (edge_adj .. |>.mpr ⟨Or.inl ⟨rfl,rfl⟩,hva⟩))

omit [Fintype V] in
lemma unsmooth_right (A : SimpleGraph V) {v a b : V} (hvb : v ≠ b) :
    (unsmooth A v a b).Adj v b := Or.inr (edge_adj .. |>.mpr ⟨Or.inl ⟨rfl,rfl⟩,hvb⟩)

omit [Fintype V] in
lemma base_le_unsmooth (A : SimpleGraph V) (v a b : V) : A ≤ unsmooth A v a b :=
  le_sup_of_le_left le_sup_left

lemma add_edge_degree (A : SimpleGraph V) {a b : V} (hab : a ≠ b) (hn : ¬A.Adj a b) (x : V) :
    (A ⊔ edge a b).degree x = A.degree x + if x = a ∨ x = b then 1 else 0 := by
  have hd : Disjoint A.edgeSet (edge a b).edgeSet := by
    rw [edge_edgeSet_of_ne hab,Set.disjoint_singleton_right]
    exact hn
  have hh := degree_sup_of_edge_disjoint A (edge a b) hd x
  have he := TwoTerminalGluing.degree_edge_eq hab x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh he ⊢
  rwa [he] at hh

lemma degree_relation (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b) (x : V) :
    (smooth A a b).degree x + (if x = v then 2 else 0) = (unsmooth A v a b).degree x := by
  have hn' : ¬(A ⊔ edge v a).Adj v b := by
    rintro (h | h)
    · exact hnb h
    · have hh := (edge_adj v a v b).mp h
      rcases hh.1 with ⟨_,h⟩ | ⟨h,_⟩
      · exact hab h.symm
      · exact hva h
  have h₁ := add_edge_degree A hab hnab x
  have h₂ := add_edge_degree A hva hna x
  have h₃ := add_edge_degree (A ⊔ edge v a) hvb hn' x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h₁ h₂ h₃ ⊢
  change Nat.card ((A ⊔ edge a b).neighborSet x) + _ =
    Nat.card (((A ⊔ edge v a) ⊔ edge v b).neighborSet x)
  rw [h₁,h₃,h₂]
  by_cases hxv : x = v
  · subst x; simp [hva,hvb]
  · by_cases hxa : x = a
    · subst x; simp [hva.symm,hab]
    · by_cases hxb : x = b
      · subst x; simp [hvb.symm,hab.symm]
      · simp [hxv,hxa,hxb]

lemma smooth_even (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (he : ∀ x, Even ((unsmooth A v a b).degree x)) :
    ∀ x, Even ((smooth A a b).degree x) := by
  intro x
  have hd := degree_relation A hva hvb hab hna hnb hnab x
  have hx := he x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hx ⊢
  rw [← hd] at hx
  by_cases hxv : x = v
  · simp only [if_pos hxv,Nat.even_add,even_two,iff_true] at hx
    exact hx
  · simpa only [if_neg hxv,Nat.add_zero] using hx

lemma edge_card_relation (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b) :
    (smooth A a b).edgeSet.ncard + 1 = (unsmooth A v a b).edgeSet.ncard := by
  have he : s(v,b) ≠ s(v,a) := fun h => hab (Sym2.congr_right.mp h).symm
  rw [smooth_edges A hab,unsmooth_edges A hva hvb]
  rw [Set.ncard_insert_of_notMem (show s(a,b) ∉ A.edgeSet from hnab),Set.ncard_insert_of_notMem (show s(v,b) ∉ insert s(v,a) A.edgeSet from by
    intro h
    rcases h with h | h
    · exact he h
    · exact hnb h),Set.ncard_insert_of_notMem (show s(v,a) ∉ A.edgeSet from hna)]

/-- A cycle using the smoothing edge but avoiding v lifts to a genuine cycle,
not just a closed trail. -/
lemma lift_avoiding_cycle (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (H : (smooth A a b).Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (he : H.Adj a b) (hv : v ∉ H.verts) :
    ∃ J : (unsmooth A v a b).Subgraph,
      (J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      J.edgeSet = insert s(v,a) (insert s(v,b) (H.edgeSet \ {s(a,b)})) := by
  obtain ⟨p,hp,hpe,hpv⟩ := TwoTerminalGluing.cycle_complementary_path H hc.1 hc.2 he
  let G := unsmooth A v a b
  have htrans : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
    intro e he
    have hh := (hpe e).mp he
    have hg := H.edgeSet_subset hh.1
    rw [smooth_edges A hab] at hg
    exact edgeSet_mono (base_le_unsmooth A v a b) (hg.resolve_left hh.2)
  let q := p.transfer G htrans
  have hq : q.IsPath := hp.transfer htrans
  have hvq : v ∉ q.support := by
    intro h
    exact hv (hpv v (by simpa [q] using h))
  let r := q.cons (unsmooth_right A hvb)
  have hr : r.IsPath := hq.cons hvq
  have hlen : 2 ≤ r.length := by
    have hh := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hab.symm (p := p))
    change 2 ≤ q.length + 1
    rw [show q.length = p.length from p.length_transfer htrans]
    omega
  let c := r.cons (unsmooth_left A hva).symm
  have hcy : c.IsCycle := path_close_isCycle r hr hlen (unsmooth_left A hva).symm
  refine ⟨c.toSubgraph,cycle_subgraph_regular G hcy,?_⟩
  ext e
  simp only [Walk.mem_edges_toSubgraph,c,r,Walk.edges_cons,List.mem_cons,
    Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff,Sym2.eq_swap]
  rw [show q.edges = p.edges from p.edges_transfer htrans,hpe]

lemma residual_eq (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (H : (smooth A a b).Subgraph) (he : H.Adj a b)
    (J : (unsmooth A v a b).Subgraph)
    (hJ : J.edgeSet = insert s(v,a) (insert s(v,b) (H.edgeSet \ {s(a,b)}))) :
    smooth A a b \ H.spanningCoe = unsmooth A v a b \ J.spanningCoe := by
  apply SimpleGraph.edgeSet_injective
  simp only [SimpleGraph.edgeSet_sdiff]
  change (smooth A a b).edgeSet \ H.edgeSet = (unsmooth A v a b).edgeSet \ J.edgeSet
  rw [smooth_edges A hab,unsmooth_edges A hva hvb,hJ]
  ext e
  have h₀ : e = s(a,b) → e ∉ A.edgeSet := by rintro rfl; exact hnab
  have h₁ : e = s(v,a) → e ∉ A.edgeSet := by rintro rfl; exact hna
  have h₂ : e = s(v,b) → e ∉ A.edgeSet := by rintro rfl; exact hnb
  have h₃ : e = s(a,b) → e ∈ H.edgeSet := by rintro rfl; exact he
  simp only [Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

/-- The complementary pieces have the same residual edge set before and after
lifting the one marked cycle. Thus no global path re-pairing is needed. -/
lemma lift_decomposition_avoiding (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (D : Finset (smooth A a b).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (smooth A a b) D)
    (H : (smooth A a b).Subgraph) (hH : H ∈ D) (he : H.Adj a b) (hv : v ∉ H.verts) :
    HasPieceBound D.card (unsmooth A v a b) := by
  obtain ⟨J,hcJ,hJe⟩ := lift_avoiding_cycle A hva hvb hab H (hc H hH) he hv
  have hEq := residual_eq A hva hvb hab hna hnb hnab H he J hJe
  obtain ⟨E,hcE,hdE,hbE⟩ := erase_cycle_piece D hc hd H hH
  have hres : HasPieceBound (D.card-1) (unsmooth A v a b \ J.spanningCoe) := by
    rw [← hEq]
    refine ⟨E,?_,hdE,by omega⟩
    intro K hK
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcE K hK
  have hres' : HasPieceBound (D.card-1)
      (unsmooth A v a b \ unionPieces (unsmooth A v a b) {J}) := by
    simpa only [unionPieces,Finset.sup_singleton] using hres
  obtain ⟨F,hcF,hdF,hbF⟩ := hres'
  obtain ⟨R,hcR,hdR,hbR⟩ := complete_cycle_packing (unsmooth A v a b) {J}
    (by intro K hK; obtain rfl := Finset.mem_singleton.mp hK; exact hcJ)
    (by simp) F (by
      intro K hK
      simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using hcF K hK) hdF
  refine ⟨R,?_,hdR,?_⟩
  · intro K hK
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcR K hK
  ·
    have hDpos := Finset.card_pos.mpr (show D.Nonempty from ⟨H,hH⟩)
    simp only [Finset.card_singleton] at hbR
    omega

lemma marked_piece_must_meet_apex (B : ℕ) (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (hbad : ¬HasPieceBound B (unsmooth A v a b))
    (D : Finset (smooth A a b).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (smooth A a b) D) (hB : D.card ≤ B)
    (H : (smooth A a b).Subgraph) (hH : H ∈ D) (he : H.Adj a b) : v ∈ H.verts := by
  by_contra hv
  obtain ⟨E,hcE,hdE,hbE⟩ := lift_decomposition_avoiding A hva hvb hab hna hnb hnab D hc hd H hH he hv
  exact hbad ⟨E,hcE,hdE,hbE.trans hB⟩

lemma lex_minimal_smoothing_obstruction (C : ℕ) (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (hG : GlobalVertexMinimal.IsLexMinimal C (unsmooth A v a b)) :
    ∃ D : Finset (smooth A a b).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (smooth A a b) D ∧ D.card ≤ C * Fintype.card V ∧
      ∀ H ∈ D, H.Adj a b → v ∈ H.verts := by
  have he := smooth_even A hva hvb hab hna hnb hnab hG.1.1
  have hcard := edge_card_relation A hva hvb hab hna hnb hnab
  obtain ⟨D,hc,hd,hb⟩ := hG.2 (smooth A a b) rfl (by omega) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he x)
  refine ⟨D,hc,hd,hb,?_⟩
  exact marked_piece_must_meet_apex (C * Fintype.card V) A hva hvb hab hna hnb hnab
    hG.1.2.1 D hc hd hb

end Erdos184.PartialSmoothing
