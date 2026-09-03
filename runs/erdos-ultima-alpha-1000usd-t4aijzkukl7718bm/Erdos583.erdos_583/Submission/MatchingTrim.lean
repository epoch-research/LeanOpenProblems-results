import Submission.Work

/-! Quantitative trimming of path partitions by a matching. -/
open SimpleGraph Erdos583Work
namespace Erdos583MatchingTrimDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma spanningCoe_acyclic_of_coe {V : Type*} {H : SimpleGraph V} (K : H.Subgraph)
    (hK : K.coe.IsAcyclic) : K.spanningCoe.IsAcyclic := by
  intro v c hc
  have hv (x : c.toSubgraph.verts) : x.val ∈ K.verts := by
    have hn := hc.ncard_neighborSet_toSubgraph_eq_two
      ((c.mem_verts_toSubgraph).mp x.property)
    have hpos : 0 < (c.toSubgraph.neighborSet x.val).ncard := by omega
    obtain ⟨y,hy⟩ := (Set.ncard_pos c.finite_neighborSet_toSubgraph).mp hpos
    exact K.edge_vert (c.toSubgraph.adj_sub hy)
  let f : c.toSubgraph.coe →g K.coe :=
    { toFun := fun x ↦ ⟨x.val,hv x⟩
      map_rel' := fun h ↦ c.toSubgraph.adj_sub h }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : K.verts ↦ z.val) h
  have ha := hK.comap f hf
  have hcc : c.mapToSubgraph.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective c.toSubgraph.hom_injective).mp
    simpa only [Walk.map_mapToSubgraph_hom] using hc
  exact ha _ hcc

lemma path_spanningCoe_isAcyclic {V : Type*} [Fintype V] {H : SimpleGraph V}
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) : p.toSubgraph.spanningCoe.IsAcyclic := by
  apply spanningCoe_acyclic_of_coe
  apply (isTree_iff_connected_and_card.mpr ⟨p.toSubgraph_connected.coe,?_⟩).IsAcyclic
  rw [InducedBuffer.subgraph_coe_edge_card,path_edgeSet_ncard hp]
  exact (InducedBuffer.path_vertex_ncard p hp).symm

/-- Restricting a path to any spanning subgraph gives a forest, so its exact
minimum number of surviving path pieces is half its number of odd vertices. -/
lemma restrict_path_partition {V : Type*} [Fintype V] {H J : SimpleGraph V}
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) :
    ∃ E : Finset J.Subgraph,
      (∀ K ∈ E, IsPathSubgraph K) ∧
      Set.PairwiseDisjoint (E : Set J.Subgraph) (fun K ↦ K.edgeSet) ∧
      (⋃ K ∈ E, K.edgeSet)=p.toSubgraph.edgeSet ∩ J.edgeSet ∧
      2*E.card=Nat.card {v // Odd ((p.toSubgraph.spanningCoe ⊓ J).degree v)} := by
  classical
  let A := p.toSubgraph.spanningCoe ⊓ J
  have hA : A.IsAcyclic := (path_spanningCoe_isAcyclic p hp).anti inf_le_left
  obtain ⟨D,hD,hcard⟩ := forest_decomposition_odd A hA
  let f : A.Subgraph → J.Subgraph := Subgraph.map (Hom.ofLE inf_le_right)
  refine ⟨D.image f,?_,?_,?_,?_⟩
  · intro K hK
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact lift_path_subgraph inf_le_right (hD.1 L hL)
  · exact hD.2.lift_pairwise inf_le_right
  · rw [hD.2.lift_union inf_le_right,edgeSet_inf]
    rfl
  · rw [Finset.card_image_of_injective _ (lift_subgraph_injective inf_le_right)]
    simpa only [Nat.card_eq_fintype_card] using hcard

/-- Terminal incidences of the deleted matching in a single path subgraph. -/
noncomputable def terminalVertices {V : Type*} [Fintype V] {H : SimpleGraph V}
    (K : H.Subgraph) (F : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v ↦ (K.neighborSet v).ncard=1 ∧
    ((K.spanningCoe ⊓ F).neighborSet v).ncard=1)

lemma odd_degree_after_matching {d a b : ℕ} (hd : d ≤ 2) (hb : b ≤ 1) (hs : a+b=d) :
    (if Odd a then 1 else 0)+2*(if d=1 ∧ b=1 then 1 else 0) =
      (if Odd d then 1 else 0)+b := by
  simp only [Nat.odd_iff]
  split_ifs <;> omega

lemma trim_odd_card {V : Type*} [Fintype V] {H : SimpleGraph V}
    (F : SimpleGraph V) (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) (hn : ¬p.Nil) :
    Nat.card {v // Odd ((p.toSubgraph.spanningCoe \ F).degree v)} +
      2*(terminalVertices p.toSubgraph F).card =
        2+2*(p.toSubgraph.edgeSet ∩ F.edgeSet).ncard := by
  classical
  let P := p.toSubgraph.spanningCoe
  let A := P \ F
  let B := P ⊓ F
  letI : DecidableRel A.Adj := Classical.decRel _
  letI : DecidableRel B.Adj := Classical.decRel _
  have hdeg (v) : (A.neighborSet v).ncard + (B.neighborSet v).ncard =
      (p.toSubgraph.neighborSet v).ncard := by
    have h := Set.ncard_inter_add_ncard_diff_eq_ncard (P.neighborSet v) (F.neighborSet v)
    change (B.neighborSet v).ncard+(A.neighborSet v).ncard=_ at h
    change (A.neighborSet v).ncard + (B.neighborSet v).ncard = (P.neighborSet v).ncard
    omega
  have hle (v) : (B.neighborSet v).ncard ≤ 1 := by
    apply (Set.ncard_le_one (Set.toFinite _)).mpr
    intro x hx y hy
    exact hm v hx.2 hy.2
  have hid (v) := odd_degree_after_matching
    (path_neighbor_ncard_le_two ⟨a,b,p,hp,rfl⟩ v) (hle v) (hdeg v)
  have hs := Finset.sum_congr rfl (fun v (_ : v ∈ (Finset.univ : Finset V)) ↦ hid v)
  have hAdeg (v) : (A.neighborSet v).ncard=A.degree v := neighborSet_ncard _ _
  have hBdeg (v) : (B.neighborSet v).ncard=B.degree v := neighborSet_ncard _ _
  simp_rw [Finset.sum_add_distrib,←Finset.mul_sum,hAdeg,hBdeg] at hs
  have hab : a ≠ b := by
    intro he; subst b
    exact hn ((Walk.isPath_iff_eq_nil p).mp hp ▸ Walk.Nil.nil)
  have hodd (v) : Odd (p.toSubgraph.neighborSet v).ncard ↔ v=a ∨ v=b := by
    exact (trail_neighbor_ncard_odd_iff hp.isTrail v).trans (and_iff_right hab)
  have hsum : (∑ v : V, if Odd (p.toSubgraph.neighborSet v).ncard then 1 else 0)=2 := by
    simp_rw [hodd]
    have he (v : V) : (if v=a ∨ v=b then 1 else 0) =
        (if v=a then 1 else 0)+(if v=b then 1 else 0) := by
      by_cases hva : v=a
      · subst v; simp [hab]
      · by_cases hvb : v=b
        · subst v; simp [hab.symm]
        · simp [hva,hvb]
    simp_rw [he,Finset.sum_add_distrib]
    simp
  rw [hsum,B.sum_degrees_eq_twice_card_edges] at hs
  have hterm : (∑ v : V, if (p.toSubgraph.neighborSet v).ncard=1 ∧ B.degree v=1 then 1 else 0) =
      (terminalVertices p.toSubgraph F).card := by
    simp_rw [←hBdeg]
    exact Finset.sum_boole _ _
  rw [hterm] at hs
  have hcA : (∑ v : V, if Odd (A.degree v) then 1 else 0)=
      Nat.card {v // Odd (A.degree v)} := by
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hcA] at hs
  conv_rhs at hs => rw [←Set.ncard_coe_finset,coe_edgeFinset]
  have hBcard : B.edgeSet.ncard=(p.toSubgraph.edgeSet ∩ F.edgeSet).ncard := by
    change (P ⊓ F).edgeSet.ncard=_
    rw [edgeSet_inf]
    rfl
  rw [hBcard] at hs
  simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hs

/-- Exact local trimming cost. A terminal matching incidence saves one unit
against the naive cost of deleting all matching edges separately. -/
lemma trim_path_partition {V : Type*} [Fintype V] {H : SimpleGraph V}
    (F : SimpleGraph V) (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) (hn : ¬p.Nil) :
    ∃ E : Finset (H \ F).Subgraph,
      (∀ K ∈ E, IsPathSubgraph K) ∧
      Set.PairwiseDisjoint (E : Set (H \ F).Subgraph) (fun K ↦ K.edgeSet) ∧
      (⋃ K ∈ E, K.edgeSet)=p.toSubgraph.edgeSet ∩ (H \ F).edgeSet ∧
      E.card+(terminalVertices p.toSubgraph F).card=1+(p.toSubgraph.edgeSet ∩ F.edgeSet).ncard := by
  classical
  obtain ⟨E,hpE,hdE,hcE,hnE⟩ := restrict_path_partition (J := H \ F) p hp
  have ht := trim_odd_card F hm p hp hn
  have hg : p.toSubgraph.spanningCoe ⊓ (H \ F)=p.toSubgraph.spanningCoe \ F := by
    ext x y
    constructor
    · rintro ⟨h,_,hn⟩; exact ⟨h,hn⟩
    · rintro ⟨h,hn⟩; exact ⟨h,p.toSubgraph.adj_sub h,hn⟩
  simp only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hnE ht
  rw [hg] at hnE
  exact ⟨E,hpE,hdE,hcE,by omega⟩

noncomputable def terminalWeight {V : Type*} [Fintype V] {H : SimpleGraph V}
    (D : Finset H.Subgraph) (F : SimpleGraph V) : ℕ :=
  ∑ K ∈ D, (terminalVertices K F).card

/-- Quantitative matching deletion: the total number of surviving pieces plus
terminal incidences is at most the original path count plus the deleted edges.
Unlike simultaneous terminality, this permits internal deleted edges compensated
by deleted singleton paths. -/
lemma trim_decomposition {V : Type*} [Fintype V] {H : SimpleGraph V}
    (F : SimpleGraph V) (hFH : F ≤ H) (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) :
    ∃ E : Finset (H \ F).Subgraph, GoodDecomposition (H \ F) E ∧
      E.card+terminalWeight D F ≤ D.card+F.edgeSet.ncard := by
  classical
  have hparts (K : D) :
      ∃ E : Finset (H \ F).Subgraph,
        (∀ L ∈ E, IsPathSubgraph L) ∧
        Set.PairwiseDisjoint (E : Set (H \ F).Subgraph) (fun L ↦ L.edgeSet) ∧
        (⋃ L ∈ E, L.edgeSet)=K.val.edgeSet ∩ (H \ F).edgeSet ∧
        E.card+(terminalVertices K.val F).card=1+(K.val.edgeSet ∩ F.edgeSet).ncard := by
    obtain ⟨a,b,p,hp,hK⟩ := hD.1 K.val K.property
    have hn : ¬p.Nil := by
      intro hn
      obtain ⟨e,he⟩ := hne K.val K.property
      rw [hK] at he
      cases hn
      simp at he
    rw [hK]
    exact trim_path_partition F hm p hp hn
  choose f hp hd hc hn using hparts
  obtain ⟨E,hE,hbound⟩ := refine_decomposition sdiff_le hD f hp hd hc
  have hs := Finset.sum_congr rfl (fun K (_ : K ∈ (Finset.univ : Finset D)) ↦ hn K)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,mul_one] at hs
  rw [Finset.sum_coe_sort D (fun K ↦ (terminalVertices K F).card),
    Finset.sum_coe_sort D (fun K ↦ (K.edgeSet ∩ F.edgeSet).ncard)] at hs
  have hi := hD.2.ncard_inter_eq_sum F.edgeSet
  rw [Set.inter_eq_right.mpr (edgeSet_mono hFH)] at hi
  rw [←hi] at hs
  refine ⟨E,hE,?_⟩
  change E.card+(∑ K ∈ D, (terminalVertices K F).card) ≤ D.card+F.edgeSet.ncard
  omega

lemma trim_decomposition_of_terminal_weight {V : Type*} [Fintype V] {H : SimpleGraph V}
    (F : SimpleGraph V) (hFH : F ≤ H) (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (hweight : F.edgeSet.ncard ≤ terminalWeight D F) :
    ∃ E : Finset (H \ F).Subgraph, GoodDecomposition (H \ F) E ∧ E.card ≤ D.card := by
  obtain ⟨E,hE,hbound⟩ := trim_decomposition F hFH hm hD hne
  exact ⟨E,hE,by omega⟩

lemma terminalVertices_card_le_two {V : Type*} [Fintype V] {H : SimpleGraph V}
    (F : SimpleGraph V) {K : H.Subgraph} (hpK : IsPathSubgraph K) :
    (terminalVertices K F).card ≤ 2 := by
  classical
  obtain ⟨a,b,p,hp,rfl⟩ := hpK
  have hsub : terminalVertices p.toSubgraph F ⊆ {a,b} := by
    intro v hv
    have hd := (Finset.mem_filter.mp hv).2.1
    have ho : Odd (p.toSubgraph.neighborSet v).ncard := by rw [hd]; exact odd_one
    have hh := (trail_neighbor_ncard_odd_iff hp.isTrail v).mp ho |>.2
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  exact (Finset.card_le_card hsub).trans (by by_cases h : a=b <;> simp [h])

lemma terminalWeight_le_twice_card {V : Type*} [Fintype V] {H : SimpleGraph V}
    (F : SimpleGraph V) {D : Finset H.Subgraph} (hp : ∀ K ∈ D, IsPathSubgraph K) :
    terminalWeight D F ≤ 2*D.card := by
  unfold terminalWeight
  calc
    _ ≤ ∑ _K ∈ D, 2 := Finset.sum_le_sum (fun K hK ↦ terminalVertices_card_le_two F (hp K hK))
    _ = _ := by simp [Nat.mul_comm]

/-- The bounded terminal-incidence optimization problem has an optimum. No
lower bound on its optimum is asserted. -/
lemma exists_terminal_weight_maximum {V : Type*} [Fintype V]
    (H F : SimpleGraph V) (ho : ∀ v, Odd (Nat.card (H.neighborSet v))) :
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
      (∀ K ∈ D, K.edgeSet.Nonempty) ∧ 2*D.card=Fintype.card V ∧
      ∀ E : Finset H.Subgraph, GoodDecomposition H E →
        (∀ K ∈ E, K.edgeSet.Nonempty) → 2*E.card=Fintype.card V →
        terminalWeight E F ≤ terminalWeight D F := by
  classical
  have ho' (v) : Odd (H.degree v) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho v
  obtain ⟨D,hD,hcard⟩ := TrailNormalization.all_odd_path_partition H ho'
  have hne (K) (hK : K ∈ D) : K.edgeSet.Nonempty := by
    by_contra hn
    have he : K.edgeSet=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hc := odd_vertices_le_twice_path_count H (hD.erase_empty K he)
    have hncard : Fintype.card {v // Odd (H.degree v)}=Fintype.card V := by simp [ho']
    rw [hncard] at hc
    have herase := Finset.card_erase_add_one hK
    omega
  let P (n : ℕ) := ∃ E : Finset H.Subgraph, GoodDecomposition H E ∧
    (∀ K ∈ E, K.edgeSet.Nonempty) ∧ 2*E.card=Fintype.card V ∧ terminalWeight E F=n
  have hbound := (terminalWeight_le_twice_card F hD.1).trans_eq hcard
  obtain ⟨E,hE,hEn,hEc,hEw⟩ := Nat.findGreatest_spec (P := P) hbound ⟨D,hD,hne,hcard,rfl⟩
  refine ⟨E,hE,hEn,hEc,?_⟩
  intro R hR hRn hRc
  rw [hEw]
  exact Nat.le_findGreatest ((terminalWeight_le_twice_card F hR.1).trans_eq hRc)
    ⟨R,hR,hRn,hRc,rfl⟩

universe u

/-- A sharp terminal-weight selection bound in connected matching deletions
would settle the full conjecture via the existing doubled-graph reduction. -/
lemma gallai_of_matching_terminal_weight
    (hselect : ∀ {W : Type u} [Fintype W] (H F : SimpleGraph W),
      (∀ w, Odd (Nat.card (H.neighborSet w))) → F ≤ H →
      (∀ w, (F.neighborSet w).Subsingleton) → (H \ F).Connected →
      ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        (∀ K ∈ D, K.edgeSet.Nonempty) ∧ 2*D.card=Fintype.card W ∧
        F.edgeSet.ncard ≤ terminalWeight D F)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  apply erdos_583_of_odd_matching_deletion _ G hG
  intro W _ H F ho hFH hm hconn
  obtain ⟨D,hD,hne,hcard,hweight⟩ := hselect H F ho hFH hm hconn
  obtain ⟨E,hE,hbound⟩ := trim_decomposition_of_terminal_weight F hFH hm hD hne hweight
  refine ⟨E,hE,hbound.trans ?_⟩
  have hceil := Nat.le_ceil ((Fintype.card W : ℚ)/2)
  exact_mod_cast (show (D.card : ℚ) ≤ (⌈(Fintype.card W : ℚ)/2⌉₊ : ℚ) by
    have hc : 2*(D.card : ℚ)=Fintype.card W := by exact_mod_cast hcard
    linarith)

end Erdos583MatchingTrimDevelopment
