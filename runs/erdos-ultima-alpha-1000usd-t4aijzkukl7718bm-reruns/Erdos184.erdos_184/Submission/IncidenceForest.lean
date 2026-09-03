import Submission.ShortestCycle

/-! Incidence graphs of linear cycle families in minimum decompositions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace CycleIncidence
variable {V I : Type*}

def graph (s : I → Set V) : SimpleGraph (V ⊕ I) where
  Adj a b := match a, b with
    | .inl v, .inr i => v ∈ s i
    | .inr i, .inl v => v ∈ s i
    | _, _ => False
  symm := by intro a b h; cases a <;> cases b <;> exact h
  loopless := by intro a; cases a <;> exact id

@[simp] lemma inl_inr_adj (s : I → Set V) (v : V) (i : I) :
    (graph s).Adj (.inl v) (.inr i) ↔ v ∈ s i := Iff.rfl
@[simp] lemma inr_inl_adj (s : I → Set V) (i : I) (v : V) :
    (graph s).Adj (.inr i) (.inl v) ↔ v ∈ s i := Iff.rfl

lemma side_walk (s : I → Set V) {a b : V ⊕ I} (p : (graph s).Walk a b) :
    p.length % 2 = if a.isLeft = b.isLeft then 0 else 1 := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    cases a <;> cases b <;> cases c <;>
      simp only [graph] at hab <;>
      simp only [Walk.length_cons, Sum.isLeft_inl, Sum.isLeft_inr, Bool.true_eq_false,
        Bool.false_eq_true, ↓reduceIte] at ih ⊢ <;> omega

lemma side_getVert (s : I → Set V) {a b : V ⊕ I} (p : (graph s).Walk a b)
    (k : ℕ) (hk : k ≤ p.length) :
    k % 2 = if a.isLeft = (p.getVert k).isLeft then 0 else 1 := by
  have h := side_walk s (p.take k)
  simpa only [Walk.take_length, inf_eq_left.mpr hk] using h

lemma left_even_getVert (s : I → Set V) {a : V} (p : (graph s).Walk (.inl a) (.inl a))
    (k : ℕ) : ∃ v, p.getVert (2*k) = .inl v := by
  by_cases hk : 2*k ≤ p.length
  · have h := side_getVert s p (2*k) hk
    cases heq : p.getVert (2*k) with
    | inl v => exact ⟨v, rfl⟩
    | inr i => simp [heq] at h
  · have h := p.getVert_of_length_le (by omega : p.length ≤ 2*k)
    exact ⟨a, h⟩

lemma right_odd_getVert (s : I → Set V) {a : V} (p : (graph s).Walk (.inl a) (.inl a))
    (k : ℕ) (hk : 2*k+1 ≤ p.length) : ∃ i, p.getVert (2*k+1) = .inr i := by
  have h := side_getVert s p (2*k+1) hk
  cases heq : p.getVert (2*k+1) with
  | inl v => simp [heq, Nat.add_mod] at h
  | inr i => exact ⟨i, rfl⟩

lemma cycle_length_six_le (s : I → Set V)
    (hlin : ∀ i j, i ≠ j → (s i ∩ s j).Subsingleton)
    {a : V} (p : (graph s).Walk (.inl a) (.inl a)) (hp : p.IsCycle) :
    6 ≤ p.length := by
  have heven : p.length % 2 = 0 := by simpa using side_walk s p
  have h3 := hp.three_le_length
  by_contra h6
  have hl : p.length = 4 := by omega
  obtain ⟨i, hi⟩ := right_odd_getVert s p 0 (by omega)
  obtain ⟨j, hj⟩ := right_odd_getVert s p 1 (by omega)
  obtain ⟨b, hb⟩ := left_even_getVert s p 1
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hi hj hb
  have hij : i ≠ j := by
    intro heq
    have hh := hp.getVert_injOn (x₁ := 1) (x₂ := 3) (by simp [hl]) (by simp [hl])
      (by rw [hi, hj, heq])
    omega
  have hab : a ≠ b := by
    intro heq
    have hh := hp.getVert_injOn' (x₁ := 0) (x₂ := 2) (by simp [hl]) (by simp [hl])
      (by rw [Walk.getVert_zero, hb, heq])
    omega
  have haI : a ∈ s i := by
    have hh := p.adj_getVert_succ (i := 0) (by omega)
    simpa only [Walk.getVert_zero, hi, inl_inr_adj] using hh
  have hbI : b ∈ s i := by
    have hh := p.adj_getVert_succ (i := 1) (by omega)
    simpa only [hi, hb, inr_inl_adj] using hh
  have hbJ : b ∈ s j := by
    have hh := p.adj_getVert_succ (i := 2) (by omega)
    simpa only [hb, hj, inl_inr_adj] using hh
  have haJ : a ∈ s j := by
    have hh := p.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1 = p.length by omega, Walk.getVert_length, hj] at hh
    exact hh
  exact hab (hlin i j hij ⟨haI,haJ⟩ ⟨hbI,hbJ⟩)

lemma exists_shortest_left (s : I → Set V) (h : ¬(graph s).IsAcyclic) :
    ∃ a : V, ∃ p : (graph s).Walk (.inl a) (.inl a),
      p.IsCycle ∧ (graph s).girth = p.length := by
  obtain ⟨a, p, hp, hg⟩ := SimpleGraph.exists_girth_eq_length.mpr h
  cases a with
  | inl a => exact ⟨a,p,hp,hg⟩
  | inr i =>
    have hadj := p.adj_snd hp.not_nil
    cases heq : p.snd with
    | inr j => simp only [heq, graph] at hadj
    | inl a =>
      have ha : Sum.inl a ∈ p.support := by
        rw [← heq]
        exact p.getVert_mem_support 1
      let q := p.rotate ha
      have hlen : q.length = p.length := by
        simpa only [Walk.length_edges] using (p.rotate_edges ha).perm.length_eq
      exact ⟨a,q,hp.rotate ha,hg.trans hlen.symm⟩

/-- A cycle in the incidence graph of a linear set family yields a clean
ring of at least three distinct sets. -/
lemma exists_clean_ring (s : I → Set V)
    (hlin : ∀ i j, i ≠ j → (s i ∩ s j).Subsingleton)
    (hnot : ¬(graph s).IsAcyclic) :
    ∃ (n : ℕ) (v : ℕ → V) (j : ∀ i, i < n → I),
      3 ≤ n ∧ v n = v 0 ∧
      Function.Injective (fun i : Fin n => j i.val i.isLt) ∧
      (∀ i, i < n → v i ≠ v (i+1)) ∧
      (∀ i hi, v i ∈ s (j i hi)) ∧
      (∀ i hi, v (i+1) ∈ s (j i hi)) ∧
      ∀ i hi k hk, i ≠ k → ∀ x,
        x ∈ s (j i hi) → x ∈ s (j k hk) → x = v i ∨ x = v k := by
  obtain ⟨a,p,hp,hg⟩ := exists_shortest_left s hnot
  have hsix := cycle_length_six_le s hlin p hp
  have heven : Even p.length := Nat.even_iff.mpr (by simpa using side_walk s p)
  obtain ⟨n, hlen⟩ := heven
  have hl : p.length = 2*n := by omega
  have hn : 3 ≤ n := by omega
  choose v hv using left_even_getVert s p
  have hodd : ∀ i, i < n → ∃ j, p.getVert (2*i+1) = Sum.inr j := by
    intro i hi
    exact right_odd_getVert s p i (by omega)
  choose j hj using hodd
  have hindex : ∀ i, i < n → 2*i+1 < p.length := by omega
  have hinj : Function.Injective (fun i : Fin n => j i.val i.isLt) := by
    intro i k heq
    dsimp only at heq
    apply Fin.ext
    have h := hp.getVert_injOn (x₁ := 2*i.val+1) (x₂ := 2*k.val+1)
      (by simp only [Set.mem_setOf_eq]; constructor <;> omega)
      (by simp only [Set.mem_setOf_eq]; constructor <;> omega)
      (by rw [hj i.val i.isLt, hj k.val k.isLt, heq])
    omega
  have hclose : v n = v 0 := by
    apply Sum.inl_injective (β := I)
    rw [← hv n, ← hv 0, ← hl]
    simp only [Nat.mul_zero, Walk.getVert_length, Walk.getVert_zero]
  have hne : ∀ i, i < n → v i ≠ v (i+1) := by
    intro i hi heq
    have hh : p.getVert (2*i) = p.getVert (2*(i+1)) := by rw [hv, hv, heq]
    by_cases hzero : i = 0
    · subst i
      have h := hp.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hh
      omega
    · have h := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; constructor <;> omega)
        (by simp only [Set.mem_setOf_eq]; constructor <;> omega) hh
      omega
  have hstart : ∀ i hi, v i ∈ s (j i hi) := by
    intro i hi
    have h := p.adj_getVert_succ (i := 2*i) (by omega)
    rw [hv, hj i hi] at h
    exact h
  have hnext : ∀ i hi, v (i+1) ∈ s (j i hi) := by
    intro i hi
    have h := p.adj_getVert_succ (hindex i hi)
    rw [show 2*i+1+1 = 2*(i+1) by omega, hv, hj i hi] at h
    exact h
  refine ⟨n,v,j,hn,hclose,hinj,hne,hstart,hnext,?_⟩
  intro i hi k hk hik x hxi hxk
  have hne' : p.getVert (2*i+1) ≠ p.getVert (2*k+1) := by
    intro heq
    have h := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; constructor <;> omega)
      (by simp only [Set.mem_setOf_eq]; constructor <;> omega) heq
    omega
  have hix : (graph s).Adj (p.getVert (2*i+1)) (Sum.inl x) := by rw [hj i hi]; exact hxi
  have hkx : (graph s).Adj (p.getVert (2*k+1)) (Sum.inl x) := by rw [hj k hk]; exact hxk
  have hxcycle : Sum.inl x ∈ p.support := ShortestCycle.common_neighbor_mem_support p hp hg
    (by omega) (p.getVert_mem_support _) (p.getVert_mem_support _) hne' hix hkx
  have hadj := ShortestCycle.isInduced p hp hg
  have hnear : ∀ t ht, x ∈ s (j t ht) → x = v t ∨ x = v (t+1) := by
    intro t ht hxt
    have htx : (graph s).Adj (p.getVert (2*t+1)) (Sum.inl x) := by rw [hj t ht]; exact hxt
    have hh := hadj (p.mem_verts_toSubgraph.mpr (p.getVert_mem_support _))
      (p.mem_verts_toSubgraph.mpr hxcycle) htx
    change Sum.inl x ∈ p.toSubgraph.neighborSet (p.getVert (2*t+1)) at hh
    rw [hp.neighborSet_toSubgraph_internal (by omega) (hindex t ht),
      show 2*t+1-1 = 2*t by omega, show 2*t+1+1 = 2*(t+1) by omega, hv, hv] at hh
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq] using hh
  rcases hnear i hi hxi with hx | hx
  · exact Or.inl hx
  rcases hnear k hk hxk with hx' | hx'
  · exact Or.inr hx'
  have heq : p.getVert (2*(i+1)) = p.getVert (2*(k+1)) := by rw [hv,hv,← hx,← hx']
  have h := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; constructor <;> omega)
    (by simp only [Set.mem_setOf_eq]; constructor <;> omega) heq
  omega

lemma degree_inr [Fintype V] [Fintype I] (s : I → Set V) (i : I) :
    (graph s).degree (.inr i) = (s i).ncard := by
  let e : (graph s).neighborSet (.inr i) ≃ s i := {
    toFun := fun w => by
      obtain ⟨w,hw⟩ := w
      cases w with
      | inl v => exact ⟨v,hw⟩
      | inr j => exact hw.elim
    invFun := fun v => ⟨.inl v.val,v.property⟩
    left_inv := by
      rintro ⟨w,hw⟩
      cases w with
      | inl v => rfl
      | inr j => exact hw.elim
    right_inv := by intro v; rfl }
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using Nat.card_congr e

lemma edge_card [Fintype V] [Fintype I] (s : I → Set V) :
    (graph s).edgeFinset.card = ∑ i, (s i).ncard := by
  let L : Finset (V ⊕ I) := Finset.univ.filter (fun x => x.isLeft)
  let R : Finset (V ⊕ I) := Finset.univ.filter (fun x => !x.isLeft)
  have hb : (graph s).IsBipartiteWith L R := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxL hxR
      simp only [L,R,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hxL hxR
      simp_all
    · intro a b hab
      cases a <;> cases b <;> simp_all [graph,L,R]
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hb
  simp only [R, Finset.sum_filter, Fintype.sum_sum_type, Sum.isLeft_inl, Sum.isLeft_inr,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
    zero_add, degree_inr] at h
  exact h.symm

lemma forest_card_bound [Fintype V] [Fintype I] (s : I → Set V)
    (hsize : ∀ i, 3 ≤ (s i).ncard) (ha : (graph s).IsAcyclic) :
    2 * Fintype.card I ≤ Fintype.card V := by
  cases isEmpty_or_nonempty I with
  | inl hi => simp
  | inr hi =>
    have hforest := forest_edge_card_lt_vertex_card (graph s) ha
    rw [edge_card, Fintype.card_sum] at hforest
    have hsum : 3 * Fintype.card I ≤ ∑ i, (s i).ncard := by
      calc
        3 * Fintype.card I = ∑ _i : I, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ i, (s i).ncard := Finset.sum_le_sum (fun i _ => hsize i)
    omega

/-- The incidence graph of a pairwise-one-vertex-overlapping subfamily of
any globally minimum cycle decomposition is a forest. -/
lemma minimum_linear_subfamily_acyclic [Fintype V] {G : SimpleGraph V}
    (D S : Finset G.Subgraph) (hSD : S ⊆ D)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (hlin : ∀ H ∈ S, ∀ K ∈ S, H ≠ K → (H.verts ∩ K.verts).Subsingleton) :
    (graph (fun H : S => H.val.verts)).IsAcyclic := by
  by_contra hnot
  have hlin' : ∀ H K : S, H ≠ K → (H.val.verts ∩ K.val.verts).Subsingleton := by
    intro H K hne
    exact hlin H.val H.property K.val K.property (fun h => hne (Subtype.ext h))
  obtain ⟨n,v,j,hn,hclose,hinj,hne,hstart,hnext,hinter⟩ :=
    exists_clean_ring (fun H : S => H.val.verts) hlin' hnot
  have hmin := CycleRing.minimum_clean_ring_subgraphs D hc hd hm v n
    (fun i hi => (j i hi).val) (fun i hi => hSD (j i hi).property)
    (by
      intro i k hik
      apply hinj
      exact Subtype.ext hik)
    (by omega) hclose hne hstart hnext hinter
  omega

/-- Linear subfamilies of a minimum cycle decomposition have at most n/2 pieces. -/
lemma minimum_linear_subfamily_card_bound [Fintype V] {G : SimpleGraph V}
    (D S : Finset G.Subgraph) (hSD : S ⊆ D)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card)
    (hlin : ∀ H ∈ S, ∀ K ∈ S, H ≠ K → (H.verts ∩ K.verts).Subsingleton) :
    2 * S.card ≤ Fintype.card V := by
  have ha := minimum_linear_subfamily_acyclic D S hSD hc hd hm hlin
  have hsize : ∀ H : S, 3 ≤ H.val.verts.ncard := by
    intro H
    have hh := cycle_edgeSet_three_le H.val (hc _ (hSD H.property)).1 (hc _ (hSD H.property)).2
    rwa [regular_two_edge_vertex_card H.val (hc _ (hSD H.property)).2] at hh
  simpa only [Fintype.card_coe] using forest_card_bound (fun H : S => H.val.verts) hsize ha

end CycleIncidence
end Erdos184
