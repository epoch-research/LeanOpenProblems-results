import Submission.EdgeSubdivision
import Submission.ExpandCover

/-!
Replacing a matching by a new vertex, with the exact cycle lifting cost.
The matching is disjoint from the original edge set; existing-edge pairs
are not silently treated as new edges.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace MatchingSmoothing

variable {V : Type*}

def IsMatching (M : SimpleGraph V) : Prop :=
  ∀ ⦃u v w⦄, M.Adj u v → M.Adj u w → v = w

lemma IsMatching.edge_eq_of_mem {M : SimpleGraph V} (hm : IsMatching M)
    {e d : Sym2 V} (he : e ∈ M.edgeSet) (hd : d ∈ M.edgeSet)
    {v : V} (hve : v ∈ e) (hvd : v ∈ d) : e = d := by
  obtain ⟨a,rfl⟩ := Sym2.mem_iff_exists.mp hve
  obtain ⟨b,rfl⟩ := Sym2.mem_iff_exists.mp hvd
  exact congrArg (fun x => s(v,x)) (hm he hd)

lemma mem_support_of_mem_edge {M : SimpleGraph V} {e : Sym2 V}
    (he : e ∈ M.edgeSet) {v : V} (hv : v ∈ e) : v ∈ M.support := by
  obtain ⟨u,rfl⟩ := Sym2.mem_iff_exists.mp hv
  exact ⟨u,he⟩

/-- Add a new vertex adjacent exactly to the endpoints of the matching. -/
def apex (A M : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => A.Adj u v
    | none, some v => v ∈ M.support
    | some v, none => v ∈ M.support
    | none, none => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    intro x
    cases x
    · exact id
    · exact A.loopless _

/-- Collapse the subdivision vertices of the matching to the new apex. -/
def project (A M : SimpleGraph V) :
    EdgeSubdivision.graph (A ⊔ M) M.edgeSet →g apex A M where
  toFun
    | .inl v => some v
    | .inr _ => none
  map_rel' := by
    intro x y h
    cases x <;> cases y
    · exact h.1.resolve_right h.2
    case inl.inr v e => exact mem_support_of_mem_edge e.property h.2
    case inr.inl e v => exact mem_support_of_mem_edge e.property h.2
    · exact h.elim

lemma project_node_injective {A M : SimpleGraph V} (hm : IsMatching M)
    {x y a b : V ⊕ M.edgeSet}
    (hxy : (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).Adj x y)
    (hab : (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).Adj a b)
    (hxa : project A M x = project A M a) (hyb : project A M y = project A M b) :
    x = a := by
  cases x with
  | inl u =>
    cases a with
    | inl v => exact congrArg Sum.inl (Option.some.inj hxa)
    | inr e => cases hxa
  | inr e =>
    cases a with
    | inl u => cases hxa
    | inr d =>
      cases y with
      | inr q => exact hxy.elim
      | inl v =>
        cases b with
        | inr q => exact hab.elim
        | inl u =>
          have hvu : v = u := Option.some.inj hyb
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hm.edge_eq_of_mem e.property d.property hxy.2 (hvu.symm ▸ hab.2)

lemma project_edge_injective {A M : SimpleGraph V} (hm : IsMatching M) :
    Set.InjOn (Sym2.map (project A M))
      (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).edgeSet := by
  intro e he d hd hed
  induction e using Sym2.ind with
  | h x y =>
    induction d using Sym2.ind with
    | h a b =>
      change s(project A M x,project A M y) = s(project A M a,project A M b) at hed
      rcases Sym2.eq_iff.mp hed with h | h
      · exact Sym2.eq_iff.mpr (Or.inl
          ⟨project_node_injective hm he hd h.1 h.2,
           project_node_injective hm he.symm hd.symm h.2 h.1⟩)
      · exact Sym2.eq_iff.mpr (Or.inr
          ⟨project_node_injective hm he hd.symm h.1 h.2,
           project_node_injective hm he.symm hd h.2 h.1⟩)

lemma project_edge_surjective (A M : SimpleGraph V)
    (ham : Disjoint A.edgeSet M.edgeSet) :
    Set.SurjOn (Sym2.map (project A M))
      (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).edgeSet (apex A M).edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    cases x with
    | none =>
      cases y with
      | none => exact he.elim
      | some v =>
        obtain ⟨u,hu⟩ := he
        let d : M.edgeSet := ⟨s(v,u),hu⟩
        exact ⟨s(Sum.inr d,Sum.inl v),
          show (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).Adj (.inr d) (.inl v)
            from ⟨Or.inr hu,Sym2.mem_mk_left _ _⟩,rfl⟩
    | some u =>
      cases y with
      | none =>
        obtain ⟨v,hv⟩ := he
        let d : M.edgeSet := ⟨s(u,v),hv⟩
        exact ⟨s(Sum.inl u,Sum.inr d),
          show (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).Adj (.inl u) (.inr d)
            from ⟨Or.inr hv,Sym2.mem_mk_left _ _⟩,rfl⟩
      | some v =>
        have hn : s(u,v) ∉ M.edgeSet := fun h => Set.disjoint_left.mp ham he h
        exact ⟨s(Sum.inl u,Sum.inl v),
          show (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).Adj (.inl u) (.inl v)
            from ⟨Or.inl he,hn⟩,rfl⟩

lemma project_fiber (A M : SimpleGraph V) :
    (project A M) ⁻¹' {none} = Set.range (Sum.inr : M.edgeSet → V ⊕ M.edgeSet) := by
  ext x
  cases x <;> simp [project]

lemma project_off_fiber_injective (A M : SimpleGraph V) :
    Set.InjOn (project A M) ((project A M) ⁻¹' {none})ᶜ := by
  intro x hx y hy hxy
  cases x <;> cases y
  · exact congrArg Sum.inl (Option.some.inj hxy)
  · exact (hy rfl).elim
  · exact (hx rfl).elim
  · exact (hx rfl).elim

lemma project_fiber_card [Fintype V] (A M : SimpleGraph V) :
    ((project A M) ⁻¹' {none}).ncard = M.edgeSet.ncard := by
  rw [project_fiber,Set.ncard_range_of_injective Sum.inr_injective]
  exact Nat.card_coe_set_eq _

lemma project_fiber_degree [Fintype V] (A M : SimpleGraph V)
    (x : V ⊕ M.edgeSet) (hx : project A M x = none) :
    (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).degree x = 2 := by
  cases x with
  | inl v => cases hx
  | inr e =>
    have h := EdgeSubdivision.degree_new (A ⊔ M) M.edgeSet e
      (SimpleGraph.edgeSet_mono (show M ≤ A ⊔ M from le_sup_right) e.property)
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h

lemma meets_fiber_iff (A M : SimpleGraph V)
    (H : (EdgeSubdivision.graph (A ⊔ M) M.edgeSet).Subgraph) :
    (H.verts ∩ (project A M) ⁻¹' {none}).Nonempty ↔
      ∃ e : M.edgeSet, Sum.inr e ∈ H.verts := by
  constructor
  · rintro ⟨x,hx,he⟩
    cases x with
    | inl v => cases he
    | inr e => exact ⟨e,hx⟩
  · rintro ⟨e,he⟩
    exact ⟨.inr e,he,rfl⟩

set_option maxHeartbeats 800000 in
/-- Smoothing along a matching of nonedges and lifting back costs exactly
at most r-q extra pieces. Existence of a favorable matching or decomposition
is a separate issue, not an assumption silently discharged here. -/
lemma lift_decomposition [Fintype V] (A M : SimpleGraph V)
    (hm : IsMatching M) (ham : Disjoint A.edgeSet M.edgeSet)
    (D : Finset (A ⊔ M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (A ⊔ M) D) :
    ∃ E : Finset (apex A M).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (apex A M) E ∧
      E.card + (D.filter (fun H => (H.edgeSet ∩ M.edgeSet).Nonempty)).card ≤
        D.card + M.edgeSet.ncard := by
  obtain ⟨F,hcF,hdF,hcardF,hmarkF⟩ :=
    EdgeSubdivision.transport_decomposition M.edgeSet D (by
      intro H hH
      refine ⟨(hc H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hc H hH).2 v) hd
  obtain ⟨E,hcE,hdE,hbE⟩ := SingleFiberProjection.project_decomposition
    (project A M) (project_edge_injective hm) (project_edge_surjective A M ham)
    none (project_off_fiber_injective A M) (project_fiber_degree A M) F (by
      intro H hH
      refine ⟨(hcF H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hcF H hH).2 v) hdF
  refine ⟨E,?_,hdE,?_⟩
  · intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE H hH).2 v
  · have hfilter : F.filter (fun H => (H.verts ∩ (project A M) ⁻¹' {none}).Nonempty) =
        F.filter (fun H => ∃ e : M.edgeSet, Sum.inr e ∈ H.verts) := by
      ext H
      simp only [Finset.mem_filter,meets_fiber_iff]
    have hmarkF' : (F.filter (fun H => ∃ e : M.edgeSet, Sum.inr e ∈ H.verts)).card =
        (D.filter (fun H => (H.edgeSet ∩ M.edgeSet).Nonempty)).card := by
      convert hmarkF using 1
      congr 1
      ext H
      simp only [Finset.mem_filter]
    rw [hfilter,hmarkF',hcardF,project_fiber_card] at hbE
    exact hbE

lemma IsMatching.degree_eq_indicator [Fintype V] {M : SimpleGraph V}
    (hm : IsMatching M) (v : V) : M.degree v = if v ∈ M.support then 1 else 0 := by
  by_cases hv : v ∈ M.support
  · obtain ⟨u,hu⟩ := hv
    have hfin : M.neighborFinset v = {u} := by
      ext w
      simp only [mem_neighborFinset,Finset.mem_singleton]
      exact ⟨fun h => hm h hu,fun h => h.symm ▸ hu⟩
    simp only [degree,hfin,Finset.card_singleton,if_pos (show v ∈ M.support from ⟨u,hu⟩)]
  · rw [if_neg hv]
    exact (M.degree_eq_zero_iff_notMem_support v).mpr hv

lemma IsMatching.support_card [Fintype V] {M : SimpleGraph V} (hm : IsMatching M) :
    M.support.ncard = 2 * M.edgeSet.ncard := by
  have hsum := M.sum_degrees_eq_twice_card_edges
  simp_rw [hm.degree_eq_indicator] at hsum
  rw [← Finset.card_filter] at hsum
  have hf : Finset.univ.filter (fun v : V => v ∈ M.support) = M.support.toFinset := by
    ext v
    simp
  rw [hf] at hsum
  simpa only [Set.ncard_eq_toFinset_card',edgeFinset_card,← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using hsum

lemma degree_apex_old [Fintype V] (A M : SimpleGraph V) (v : V) :
    (apex A M).degree (some v) = A.degree v + if v ∈ M.support then 1 else 0 := by
  by_cases hv : v ∈ M.support
  · have hf : (apex A M).neighborFinset (some v) =
        insert none ((A.neighborFinset v).map Function.Embedding.some) := by
      ext x
      cases x <;> simp [apex,hv]
    rw [degree,hf,Finset.card_insert_of_notMem (by simp),Finset.card_map,if_pos hv]
    rfl
  · have hf : (apex A M).neighborFinset (some v) =
        (A.neighborFinset v).map Function.Embedding.some := by
      ext x
      cases x <;> simp [apex,hv]
    rw [degree,hf,Finset.card_map,if_neg hv,Nat.add_zero]
    rfl

lemma degree_apex_new [Fintype V] (A M : SimpleGraph V) :
    (apex A M).degree none = M.support.ncard := by
  have hf : (apex A M).neighborFinset none = M.support.toFinset.map Function.Embedding.some := by
    ext x
    cases x <;> simp [apex]
  rw [degree,hf,Finset.card_map,Set.ncard_eq_toFinset_card']

lemma degree_smoothed [Fintype V] (A M : SimpleGraph V) (hm : IsMatching M)
    (ham : Disjoint A.edgeSet M.edgeSet) (v : V) :
    (A ⊔ M).degree v = (apex A M).degree (some v) := by
  have hs := degree_sup_of_edge_disjoint A M ham v
  have hmdeg := hm.degree_eq_indicator v
  have ha := degree_apex_old A M v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hs hmdeg ha ⊢
  omega

lemma even_apex_iff [Fintype V] (A M : SimpleGraph V) (hm : IsMatching M)
    (ham : Disjoint A.edgeSet M.edgeSet) :
    (∀ v, Even ((apex A M).degree v)) ↔ (∀ v, Even ((A ⊔ M).degree v)) := by
  constructor
  · intro he v
    have h := degree_smoothed A M hm ham v
    have hev := he (some v)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hev ⊢
    rwa [h]
  · intro he v
    cases v with
    | none =>
      have h := degree_apex_new A M
      have hc := hm.support_card
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
      rw [h,hc]
      exact even_two_mul _
    | some v =>
      have h := degree_smoothed A M hm ham v
      have hev := he v
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hev ⊢
      rwa [← h]

lemma marked_card_pos {A M : SimpleGraph V} (hne : M ≠ ⊥)
    (D : Finset (A ⊔ M).Subgraph) (hd : IsDecomposition (A ⊔ M) D) :
    0 < (D.filter (fun H => (H.edgeSet ∩ M.edgeSet).Nonempty)).card := by
  obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hG : s(u,v) ∈ (A ⊔ M).edgeSet := Or.inr huv
  rw [← hd.2] at hG
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp hG
  exact Finset.card_pos.mpr ⟨H,Finset.mem_filter.mpr ⟨hH,⟨s(u,v),heH,huv⟩⟩⟩

/-- The elementary one-vertex induction step justified by smoothing. The
hypothesis is a decomposition of the smaller graph, not subgraph minimality
of the larger graph. -/
lemma bound_apex_of_small_matching [Fintype V] (C : ℕ)
    (A M : SimpleGraph V) (hm : IsMatching M)
    (ham : Disjoint A.edgeSet M.edgeSet) (hne : M ≠ ⊥)
    (hr : M.edgeSet.ncard ≤ C + 1)
    (D : Finset (A ⊔ M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (A ⊔ M) D) (hb : D.card ≤ C * Fintype.card V) :
    ∃ E : Finset (apex A M).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (apex A M) E ∧ E.card ≤ C * Fintype.card (Option V) := by
  obtain ⟨E,hcE,hdE,hbE⟩ := lift_decomposition A M hm ham D hc hd
  refine ⟨E,hcE,hdE,?_⟩
  have hq := marked_card_pos hne D hd
  rw [Fintype.card_option,Nat.mul_add,Nat.mul_one]
  omega

end MatchingSmoothing
end Erdos184
