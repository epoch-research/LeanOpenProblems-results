import Submission.Work

/-! Cycle-cutting and Walecki cycle families for marked-edge constructions. -/

open SimpleGraph Erdos583Work
namespace Erdos583CycleDevelopment

lemma isCycle_append_comm {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} {q : G.Walk b a} (hc : (p.append q).IsCycle) :
    (q.append p).IsCycle := by
  have ht : (q.append p).IsTrail := by
    rw [Walk.isTrail_def, Walk.edges_append]
    exact List.nodup_append_comm.mp (by simpa only [Walk.edges_append] using hc.isTrail.edges_nodup)
  have hn : (q.append p).length ≠ 0 := by
    have hp := Walk.not_nil_iff_lt_length.mp hc.not_nil
    simp only [Walk.length_append] at hp ⊢
    omega
  refine ⟨⟨ht, fun h ↦ hn (by simp [h])⟩, ?_⟩
  rw [Walk.tail_support_append]
  exact List.nodup_append_comm.mp (by simpa only [Walk.tail_support_append] using hc.support_nodup)

/-- Deleting one edge of a simple cycle leaves a single simple path. -/
lemma exists_cycle_cut_edge {V : Type*} {G : SimpleGraph V} {a : V}
    (c : G.Walk a a) (hc : c.IsCycle) (e : Sym2 V) (he : e ∈ c.edges) :
    ∃ u v, ∃ p : G.Walk u v, p.IsPath ∧
      p.toSubgraph.edgeSet = c.toSubgraph.edgeSet \ {e} ∧ p.length+1 = c.length := by
  obtain ⟨u, v, huv, q, r, rfl, rfl⟩ := walk_split_at_edge c e he
  have hh := isCycle_append_comm hc
  change (Walk.cons huv (r.append q)).IsCycle at hh
  obtain ⟨hp, hnot⟩ := (Walk.cons_isCycle_iff _ _).mp hh
  refine ⟨v, u, r.append q, hp, ?_, ?_⟩
  · ext z
    have hnotq : s(u,v) ∉ q.edges := fun hz ↦ hnot (by simp [hz])
    have hnotr : s(u,v) ∉ r.edges := fun hz ↦ hnot (by simp [hz])
    simp only [Walk.edgeSet_toSubgraph, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Walk.edges_append, Walk.edges_cons, List.mem_append, List.mem_cons]
    aesop
  · simp only [Walk.length_append, Walk.length_cons]
    omega

namespace WaleckiCycles
open Erdos583Work.Walecki

def closePath {V : Type*} {a b : V} (p : (⊤ : SimpleGraph V).Walk a b) :
    (⊤ : SimpleGraph (Option V)).Walk none none :=
  .cons (by simp : (⊤ : SimpleGraph (Option V)).Adj none (some a))
    ((p.map (someHom V)).concat (by simp : (⊤ : SimpleGraph (Option V)).Adj (some b) none))

lemma closePath_isCycle {V : Type*} {a b : V} (p : (⊤ : SimpleGraph V).Walk a b)
    (hp : p.IsPath) (hn : ¬p.Nil) : (closePath p).IsCycle := by
  have hab : a ≠ b := by
    rintro rfl
    exact hn ((Walk.isPath_iff_eq_nil p).mp hp ▸ Walk.Nil.nil)
  rw [closePath, Walk.cons_isCycle_iff]
  constructor
  · exact (Walk.map_isPath_of_injective (Option.some_injective V) hp).concat
      (by simp [Walk.support_map, someHom]) _
  · rw [show s(none, some a) = s(some a, none) from Sym2.eq_swap]
    simp [Walk.edges_concat, Walk.edges_map, someHom, hab, map_some_ne_spoke]

lemma closePath_length {V : Type*} {a b : V} (p : (⊤ : SimpleGraph V).Walk a b) :
    (closePath p).length = p.length+2 := by simp [closePath]

lemma closePath_mem_edges {V : Type*} {a b : V} (p : (⊤ : SimpleGraph V).Walk a b)
    (e : Sym2 (Option V)) :
    e ∈ (closePath p).edges ↔ e = s(some a, none) ∨ e = s(some b, none) ∨
      ∃ e' ∈ p.edges, Sym2.map some e' = e := by
  simp [closePath, Walk.edges_map, someHom, Sym2.eq_swap, or_comm]

lemma closePath_finite_mem_edges {V : Type*} {a b : V} (p : (⊤ : SimpleGraph V).Walk a b)
    (x y : V) : s(some x, some y) ∈ (closePath p).edges ↔ s(x,y) ∈ p.edges := by
  rw [closePath_mem_edges]
  have ha : s(some x, some y) ≠ s(some a, none) := map_some_ne_spoke s(x,y) a
  have hb : s(some x, some y) ≠ s(some b, none) := map_some_ne_spoke s(x,y) b
  simp only [ha, hb, false_or]
  constructor
  · rintro ⟨e, he, heq⟩
    have : e = s(x,y) := (Sym2.map.injective (Option.some_injective V)) heq
    simpa [this] using he
  · intro he
    exact ⟨s(x,y), he, rfl⟩

lemma closePath_spoke_mem_edges {V : Type*} {a b : V} (p : (⊤ : SimpleGraph V).Walk a b)
    (x : V) : s(some x, none) ∈ (closePath p).edges ↔ x = a ∨ x = b := by
  rw [closePath_mem_edges]
  have hm : ¬∃ e' ∈ p.edges, Sym2.map some e' = s(some x, none) := by
    rintro ⟨e', _, he⟩
    exact map_some_ne_spoke e' x he
  simp [hm]

def middleA {k : ℕ} (i : Fin k) : ZMod (2*k) := vertex i ⟨k-1, by have := i.isLt; omega⟩
def middleB {k : ℕ} (i : Fin k) : ZMod (2*k) := vertex i ⟨k, by have := i.isLt; omega⟩
def middleEdge {k : ℕ} (i : Fin k) : Sym2 (Option (ZMod (2*k))) :=
  s(some (middleA i), some (middleB i))
def firstEdge {k : ℕ} (i : Fin k) : Sym2 (Option (ZMod (2*k))) :=
  s(some (i.val : ZMod (2*k)), some ((i.val : ZMod (2*k))-1))

lemma middle_ne {k : ℕ} (i : Fin k) : middleA i ≠ middleB i := by
  intro he
  have hv : k-1 = k := congrArg Fin.val (vertex_injective i he)
  have := i.isLt
  omega

lemma middleB_eq {k : ℕ} (i : Fin k) : middleB i = middleA i + (k : ZMod (2*k)) := by
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk' : k-1+1 = k := by omega
  have hh : -(k : ZMod (2*k)) = (k : ZMod (2*k)) := by
    have h2 : (k : ZMod (2*k)) + (k : ZMod (2*k)) = 0 := by
      rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
    linear_combination -h2
  have hd := WaleckiTerminal.zig_succ_difference (j := k-1) (by omega : k-1+1 < 2*k)
  rw [hk', hh] at hd
  simp only [ite_self] at hd
  dsimp only [middleA, middleB, vertex]
  linear_combination hd

lemma middle_endpoint_index {k : ℕ} (i j : Fin k) (b c : Bool)
    (he : (if b then middleB i else middleA i) =
      (if c then middleB j else middleA j)) : i = j := by
  apply endpoint_index i j b c
  cases b <;> cases c <;>
    simp only [Bool.false_eq_true, ↓reduceIte, middleB_eq,
      middleA, vertex, Nat.cast_add, add_zero] at he ⊢
  all_goals linear_combination he

lemma path_ends {k : ℕ} (i : Fin k) {a b : ZMod (2*k)}
    (p : (⊤ : SimpleGraph (ZMod (2*k))).Walk a b)
    (hs : p.support = List.ofFn (vertex i)) :
    a = (i.val : ZMod (2*k)) ∧ b = (i.val : ZMod (2*k)) + k := by
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hl : p.length+1 = 2*k := by simpa using congrArg List.length hs
  constructor
  · calc
      a = vertex i ⟨0, by omega⟩ := by
        simpa only [Walk.getVert_zero] using getVert_of_support_eq_ofFn p hs 0 (by omega)
      _ = _ := vertex_zero i _
  · have hv := getVert_of_support_eq_ofFn p hs p.length (by omega)
    rw [Walk.getVert_length] at hv
    have hv' : p.length = 2*k-1 := by omega
    simpa only [hv', vertex_last] using hv

/-- Walecki's Hamilton-cycle family, with designated first and middle edges. -/
lemma exists_cycle_family (k : ℕ) (hk : 0 < k) :
    ∃ c : Fin k → (⊤ : SimpleGraph (Option (ZMod (2*k)))).Walk none none,
      (∀ i, (c i).IsCycle ∧ (c i).length = 2*k+1 ∧
        firstEdge i ∈ (c i).edges ∧ middleEdge i ∈ (c i).edges ∧
        ∀ x y, s(some x, some y) ∈ (c i).edges → (x+y+1).val/2 = i.val) ∧
      Pairwise (fun i j ↦ Disjoint (c i).toSubgraph.edgeSet (c j).toSubgraph.edgeSet) := by
  classical
  choose a b p hp hs using exists_path_vertex (k := k)
  have hl (i : Fin k) : (p i).length+1 = 2*k := by simpa using congrArg List.length (hs i)
  have hn (i : Fin k) : ¬(p i).Nil := Walk.not_nil_iff_lt_length.mpr (by have := hl i; omega)
  let c (i : Fin k) := closePath (p i)
  have hcolor (i : Fin k) (x y : ZMod (2*k)) (he : s(some x, some y) ∈ (c i).edges) :
      (x+y+1).val/2 = i.val :=
    path_vertex_color i (p i) (hs i) ((closePath_finite_mem_edges _ _ _).mp he)
  have hspoke (i : Fin k) (x : ZMod (2*k)) :
      s(some x, none) ∈ (c i).edges ↔ x = (i.val : ZMod (2*k)) ∨ x = (i.val : ZMod (2*k))+k := by
    rw [closePath_spoke_mem_edges]
    rw [(path_ends i (p i) (hs i)).1, (path_ends i (p i) (hs i)).2]
  refine ⟨c, ?_, ?_⟩
  · intro i
    refine ⟨closePath_isCycle _ (hp i) (hn i), ?_, ?_, ?_, hcolor i⟩
    · rw [closePath_length]
      have := hl i
      omega
    · apply (closePath_finite_mem_edges _ _ _).mpr
      have he := List.getElem_mem (l := (p i).edges) (n := 0) (by have := hl i; simp; omega)
      rw [edge_getElem (p i) 0 (by have := hl i; omega),
        getVert_of_support_eq_ofFn (p i) (hs i) 0 (by omega),
        getVert_of_support_eq_ofFn (p i) (hs i) 1 (by omega)] at he
      simpa only [vertex_zero, vertex_one] using he
    · apply (closePath_finite_mem_edges _ _ _).mpr
      have he := List.getElem_mem (l := (p i).edges) (n := k-1)
        (by have := hl i; simp; omega)
      rw [edge_getElem (p i) (k-1) (by have := hl i; omega),
        getVert_of_support_eq_ofFn (p i) (hs i) (k-1) (by omega),
        getVert_of_support_eq_ofFn (p i) (hs i) (k-1+1) (by omega)] at he
      have hk' : k-1+1 = k := by omega
      simpa only [middleA, middleB, hk'] using he
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    have hei' := (c i).mem_edges_toSubgraph.mp hei
    have hej' := (c j).mem_edges_toSubgraph.mp hej
    rcases (closePath_mem_edges _ e).mp hei' with rfl | rfl | ⟨e', he', rfl⟩
    · rw [(path_ends i (p i) (hs i)).1] at hej'
      apply hij
      rcases (hspoke j _).mp hej' with h | h
      · exact endpoint_index i j false false (by simpa using h)
      · exact endpoint_index i j false true (by simpa using h)
    · rw [(path_ends i (p i) (hs i)).2] at hej'
      apply hij
      rcases (hspoke j _).mp hej' with h | h
      · exact endpoint_index i j true false (by simpa using h)
      · exact endpoint_index i j true true (by simpa using h)
    · induction e' using Sym2.ind with
      | h x y =>
        exact hij (Fin.ext ((hcolor i x y ((closePath_finite_mem_edges _ _ _).mpr he')).symm.trans
          (hcolor j x y hej')))

lemma middleEdge_injective {k : ℕ} : Function.Injective (middleEdge (k := k)) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact middle_endpoint_index i j false false (Option.some.inj ha)
  · exact middle_endpoint_index i j false true (Option.some.inj ha)

def prefixMatching (k t : ℕ) : SimpleGraph (Option (ZMod (2*k))) where
  Adj x y := ∃ i : Fin k, i.val < t ∧
    ((x = some (middleA i) ∧ y = some (middleB i)) ∨
      (x = some (middleB i) ∧ y = some (middleA i)))
  symm := by
    rintro x y ⟨i, hi, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · exact ⟨i, hi, Or.inr ⟨hb, ha⟩⟩
    · exact ⟨i, hi, Or.inl ⟨hb, ha⟩⟩
  loopless := by
    rintro x ⟨i, hi, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · exact middle_ne i (Option.some.inj (ha.symm.trans hb))
    · exact middle_ne i (Option.some.inj (hb.symm.trans ha))

lemma prefixMatching_mem {k t : ℕ} (e : Sym2 (Option (ZMod (2*k)))) :
    e ∈ (prefixMatching k t).edgeSet ↔ ∃ i : Fin k, i.val < t ∧ e = middleEdge i := by
  induction e using Sym2.ind with
  | h x y => simp [prefixMatching, middleEdge]

lemma prefixMatching_matching (k t : ℕ) :
    ∀ x, ((prefixMatching k t).neighborSet x).Subsingleton := by
  rintro x y ⟨i, hi, hxy⟩ z ⟨j, hj, hxz⟩
  rcases hxy with ⟨hxi, hy⟩ | ⟨hxi, hy⟩ <;> rcases hxz with ⟨hxj, hz⟩ | ⟨hxj, hz⟩
  · have hij := middle_endpoint_index i j false false (Option.some.inj (hxi.symm.trans hxj))
    subst j
    exact hy.trans hz.symm
  · have hij := middle_endpoint_index i j false true (Option.some.inj (hxi.symm.trans hxj))
    subst j
    exact (middle_ne i (Option.some.inj (hxi.symm.trans hxj))).elim
  · have hij := middle_endpoint_index i j true false (Option.some.inj (hxi.symm.trans hxj))
    subst j
    exact (middle_ne i (Option.some.inj (hxj.symm.trans hxi))).elim
  · have hij := middle_endpoint_index i j true true (Option.some.inj (hxi.symm.trans hxj))
    subst j
    exact hy.trans hz.symm

lemma prefixMatching_ncard {k t : ℕ} (ht : t ≤ k) : (prefixMatching k t).edgeSet.ncard = t := by
  let f (i : Fin t) := middleEdge (⟨i.val, i.isLt.trans_le ht⟩ : Fin k)
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) (middleEdge_injective (k := k) he))
  have heq : (prefixMatching k t).edgeSet = Set.range f := by
    ext e
    rw [prefixMatching_mem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.val, i.isLt.trans_le ht⟩, i.isLt, rfl⟩
  rw [heq, Set.ncard_range_of_injective hf]
  simp

lemma middle_color {k : ℕ} (i : Fin k) :
    (middleA i + middleB i + 1).val/2 = i.val := by
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hi := vertex_color i (j := k-1) (by omega)
  have he : k-1+1 = k := by omega
  simpa only [middleA, middleB, he] using hi

def shortSlice {k : ℕ} (t : ℕ) (j : Fin (k-t+1)) : ZMod (2*k) :=
  ((t+j.val : ℕ) : ZMod (2*k))-1

lemma shortSlice_injective {k t : ℕ} (hk : 0 < k) (ht : t ≤ k) :
    Function.Injective (shortSlice (k := k) t) := by
  intro i j he
  have hc : ((t+i.val : ℕ) : ZMod (2*k)) = ((t+j.val : ℕ) : ZMod (2*k)) := sub_left_inj.mp he
  have hi : t+i.val < 2*k := by have := i.isLt; omega
  have hj : t+j.val < 2*k := by have := j.isLt; omega
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hv
  exact Fin.ext (by omega)

lemma exists_short_slice (k t : ℕ) (hk : 0 < k) (ht : t ≤ k) :
    ∃ a b, ∃ p : (⊤ : SimpleGraph (ZMod (2*k))).Walk a b,
      p.IsPath ∧ p.length = k-t ∧ ∀ e ∈ p.edges,
        ∃ i : Fin k, t ≤ i.val ∧ e = s((i.val : ZMod (2*k)), (i.val : ZMod (2*k))-1) := by
  have hne : List.ofFn (shortSlice (k := k) t) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hc : (List.ofFn (shortSlice (k := k) t)).IsChain
      (⊤ : SimpleGraph (ZMod (2*k))).Adj := by
    rw [List.isChain_ofFn]
    intro j hj he
    have hval : j = j+1 := congrArg Fin.val (shortSlice_injective hk ht he)
    omega
  obtain ⟨a, b, p, hp, hs⟩ := exists_path_support hne
    (List.nodup_ofFn_ofInjective (shortSlice_injective hk ht)) hc
  have hl : p.length = k-t := by
    have := congrArg List.length hs
    simpa using this
  refine ⟨a, b, p, hp, hl, ?_⟩
  intro e he
  obtain ⟨j, hj, he⟩ := mem_edges_index p he
  rw [hl] at hj
  refine ⟨⟨t+j, by omega⟩, (by change t ≤ t+j; omega), ?_⟩
  rw [getVert_of_support_eq_ofFn p hs j (by omega),
    getVert_of_support_eq_ofFn p hs (j+1) (by omega)] at he
  have hjcast : ((t+(j+1) : ℕ) : ZMod (2*k))-1 = ((t+j : ℕ) : ZMod (2*k)) := by push_cast; ring
  simpa only [shortSlice, hjcast, Sym2.eq_swap] using he

lemma firstEdge_not_prefixMatching {k t : ℕ} (i : Fin k) (hi : t ≤ i.val) :
    firstEdge i ∉ (prefixMatching k t).edgeSet := by
  intro h
  obtain ⟨j, hj, he⟩ := (prefixMatching_mem _).mp h
  have he' : s((i.val : ZMod (2*k)), (i.val : ZMod (2*k))-1) = s(middleA j, middleB j) :=
    (Sym2.map.injective (Option.some_injective _)) he
  have hs : (i.val : ZMod (2*k)) + ((i.val : ZMod (2*k))-1) = middleA j + middleB j := by
    rcases Sym2.eq_iff.mp he' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linear_combination h₁ + h₂
  have hc : i.val = j.val := (first_color i).symm.trans (by rw [hs]; exact middle_color j)
  omega

lemma canonical_matching_decomposition (k t : ℕ) (hk : 0 < k) (ht : t ≤ k) :
    ∃ D : Finset ((prefixMatching k t)ᶜ).Subgraph,
      GoodDecomposition (prefixMatching k t)ᶜ D ∧ D.card ≤ k+1 := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  let F := prefixMatching k t
  let J := (⊤ : SimpleGraph (Option (ZMod (2*k)))) \ F
  obtain ⟨c, hc, hd⟩ := exists_cycle_family k hk
  let d (i : Fin k) := if i.val < t then middleEdge i else firstEdge i
  have he (i : Fin k) : d i ∈ (c i).edges := by
    dsimp [d]
    split_ifs
    · exact (hc i).2.2.2.1
    · exact (hc i).2.2.1
  choose a b q hq hqe hql using fun i ↦ exists_cycle_cut_edge (c i) (hc i).1 (d i) (he i)
  have hqJ (i : Fin k) : ∀ e ∈ (q i).edges, e ∈ J.edgeSet := by
    intro e he
    have hec : e ∈ (c i).toSubgraph.edgeSet \ {d i} := hqe i ▸ (q i).mem_edges_toSubgraph.mpr he
    rw [edgeSet_sdiff]
    refine ⟨(q i).edges_subset_edgeSet he, ?_⟩
    intro heF
    obtain ⟨j, hj, rfl⟩ := (prefixMatching_mem _).mp heF
    have hcol := (hc i).2.2.2.2 (middleA j) (middleB j) ((c i).mem_edges_toSubgraph.mp hec.1)
    have hij : i = j := Fin.ext (hcol.symm.trans (middle_color j))
    subst j
    exact hec.2 (by simp [d, hj])
  let r (i : Fin k) := (q i).transfer J (hqJ i)
  have hr (i : Fin k) : (r i).IsPath := (hq i).transfer (hqJ i)
  have hre (i : Fin k) : (r i).toSubgraph.edgeSet = (c i).toSubgraph.edgeSet \ {d i} := by
    simpa [r, Walk.edgeSet_toSubgraph] using hqe i
  have hrL (i : Fin k) : (r i).length = 2*k := by
    have h₁ := hql i
    have h₂ := (hc i).2.1
    simp only [r, Walk.length_transfer]
    omega
  have hdr : Pairwise (fun i j ↦ Disjoint (r i).toSubgraph.edgeSet (r j).toSubgraph.edgeSet) := by
    intro i j hij
    rw [hre, hre]
    exact (hd hij).mono Set.diff_subset Set.diff_subset
  obtain ⟨u, v, p, hp, hpL, hpe⟩ := exists_short_slice k t hk ht
  let p₀ := p.map (someHom (ZMod (2*k)))
  have hp₀ : p₀.IsPath := Walk.map_isPath_of_injective (Option.some_injective _) hp
  have hpJ : ∀ e ∈ p₀.edges, e ∈ J.edgeSet := by
    intro e he
    rw [edgeSet_sdiff]
    refine ⟨p₀.edges_subset_edgeSet he, ?_⟩
    have hmap : e ∈ p.edges.map (Sym2.map (someHom (ZMod (2*k)))) := by
      simpa only [p₀, Walk.edges_map] using he
    obtain ⟨e', he0, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨i, hi, rfl⟩ := hpe e' he0
    exact firstEdge_not_prefixMatching i hi
  let p₁ := p₀.transfer J hpJ
  have hp₁ : p₁.IsPath := hp₀.transfer hpJ
  have hd₁ (i : Fin k) : Disjoint p₁.toSubgraph.edgeSet (r i).toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hep her
    have hmap : e ∈ p.edges.map (Sym2.map (someHom (ZMod (2*k)))) := by
      simpa only [p₁, Walk.edges_transfer, p₀, Walk.edges_map] using p₁.mem_edges_toSubgraph.mp hep
    obtain ⟨e', he0, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨j, hj, rfl⟩ := hpe e' he0
    rw [hre] at her
    have hcol := (hc i).2.2.2.2 (j.val : ZMod (2*k)) ((j.val : ZMod (2*k))-1)
      ((c i).mem_edges_toSubgraph.mp her.1)
    have hij : i = j := Fin.ext (hcol.symm.trans (first_color j))
    subst j
    exact her.2 (by simp [d, show ¬i.val < t by omega, firstEdge, someHom])
  let f : Option (Fin k) → J.Subgraph
    | none => p₁.toSubgraph
    | some i => (r i).toSubgraph
  have hf (i : Option (Fin k)) : IsPathSubgraph (f i) := by
    cases i with
    | none => exact ⟨_, _, p₁, hp₁, rfl⟩
    | some i => exact ⟨_, _, r i, hr i, rfl⟩
  have hdf : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hd₁ j
    | some i =>
      cases j with
      | none => exact (hd₁ i).symm
      | some j => exact hdr (fun h ↦ hij (congrArg some h))
  have hc₁ : p₁.toSubgraph.edgeSet.ncard = k-t := by
    rw [path_edgeSet_ncard hp₁]
    simpa [p₁, p₀] using hpL
  have hci (i : Fin k) : (r i).toSubgraph.edgeSet.ncard = 2*k := by
    rw [path_edgeSet_ncard (hr i), hrL i]
  have htop : (⊤ : SimpleGraph (Option (ZMod (2*k)))).edgeSet.ncard = k*(2*k+1) := by
    rw [Set.ncard_eq_toFinset_card']
    change (⊤ : SimpleGraph (Option (ZMod (2*k)))).edgeFinset.card = _
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_option, ZMod.card, Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_comm (2*k+1), Nat.mul_assoc]
    simp
  have hJcard : J.edgeSet.ncard + t = k*(2*k+1) := by
    have hn := Set.ncard_diff_add_ncard_of_subset (edgeSet_mono (show F ≤ ⊤ from le_top))
    rw [← edgeSet_sdiff, prefixMatching_ncard ht, htop] at hn
    exact hn
  have hsum : ∑ i, (f i).edgeSet.ncard = J.edgeSet.ncard := by
    simp only [Fintype.sum_option, f, hc₁, hci, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    have hsub : k-t+t = k := Nat.sub_add_cancel ht
    nlinarith
  obtain ⟨D, hD, hn⟩ := decomposition_of_family_of_card J f hf hdf hsum
  exact ⟨D, hD, by simpa using hn⟩

end WaleckiCycles
lemma matching_edges_eq_of_mem {V : Type*} {F : SimpleGraph V}
    (hm : ∀ x, (F.neighborSet x).Subsingleton) (e f : F.edgeSet) (x : V)
    (he : x ∈ e.val) (hf : x ∈ f.val) : e = f := by
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp he
  obtain ⟨z, hz⟩ := Sym2.mem_iff_exists.mp hf
  have hxy : F.Adj x y := by
    have hh := e.property
    rw [hy, mem_edgeSet] at hh
    exact hh
  have hxz : F.Adj x z := by
    have hh := f.property
    rw [hz, mem_edgeSet] at hh
    exact hh
  have heq : y = z := hm x hxy hxz
  exact Subtype.ext (hy.trans ((congrArg (fun w ↦ s(x,w)) heq).trans hz.symm))

/-- Every matching is a set of disjoint two-vertex components on its support. -/
lemma matching_support_model {V : Type*} (F : SimpleGraph V)
    (hm : ∀ x, (F.neighborSet x).Subsingleton) :
    ∃ e : F.edgeSet × Bool ≃ F.support,
      ∀ p q, F.Adj (e p).val (e q).val ↔ p.1 = q.1 ∧ p.2 ≠ q.2 := by
  classical
  have hex (d : F.edgeSet) : ∃ a b, F.Adj a b ∧ d.val = s(a,b) := by
    obtain ⟨d, hd⟩ := d
    induction d using Sym2.ind with
    | h a b => exact ⟨a, b, hd, rfl⟩
  choose a b hab he using hex
  let v (p : F.edgeSet × Bool) := if p.2 then b p.1 else a p.1
  have hmem (p : F.edgeSet × Bool) : v p ∈ p.1.val := by
    rw [he]
    cases h : p.2 <;> simp [v, h]
  have hsupp (p : F.edgeSet × Bool) : v p ∈ F.support := by
    cases h : p.2
    · exact ⟨b p.1, by simpa [v, h] using hab p.1⟩
    · exact ⟨a p.1, by simpa [v, h] using (hab p.1).symm⟩
  let r (p : F.edgeSet × Bool) : F.support := ⟨v p, hsupp p⟩
  have hri : Function.Injective r := by
    rintro ⟨d, bd⟩ ⟨f, bf⟩ h
    have hv : v (d,bd) = v (f,bf) := congrArg Subtype.val h
    have hef : d = f := matching_edges_eq_of_mem hm d f (v (d,bd))
      (hmem _) (hv.symm ▸ hmem (f,bf))
    subst f
    have hne := (hab d).ne
    cases bd <;> cases bf
    · rfl
    · exact (hne hv).elim
    · exact (hne hv.symm).elim
    · rfl
  have hrs : Function.Surjective r := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hxy⟩ := hx
    let d : F.edgeSet := ⟨s(x,y), hxy⟩
    have hxd : x ∈ d.val := by simp [d]
    rw [he d, Sym2.mem_iff] at hxd
    rcases hxd with hx | hx
    · exact ⟨(d,false), Subtype.ext (by simpa [r, v] using hx.symm)⟩
    · exact ⟨(d,true), Subtype.ext (by simpa [r, v] using hx.symm)⟩
  let e := Equiv.ofBijective r ⟨hri, hrs⟩
  refine ⟨e, ?_⟩
  intro p q
  constructor
  · intro hpq
    let d : F.edgeSet := ⟨s(v p, v q), hpq⟩
    have hpd : p.1 = d := matching_edges_eq_of_mem hm p.1 d (v p) (hmem _) (by simp [d])
    have hqd : q.1 = d := matching_edges_eq_of_mem hm q.1 d (v q) (hmem _) (by simp [d])
    have heq : p.1 = q.1 := hpd.trans hqd.symm
    refine ⟨heq, ?_⟩
    intro hbool
    have hpq' : p = q := Prod.ext heq hbool
    subst q
    exact F.loopless _ hpq
  · rintro ⟨hedge, hbool⟩
    obtain ⟨d, bd⟩ := p
    obtain ⟨f, bf⟩ := q
    dsimp only [Prod.fst, Prod.snd] at hedge hbool
    subst f
    cases bd <;> cases bf
    · exact (hbool rfl).elim
    · simpa [e, r, v] using hab d
    · simpa [e, r, v] using (hab d).symm
    · exact (hbool rfl).elim

lemma matching_support_card {V : Type*} [Fintype V] (F : SimpleGraph V)
    (hm : ∀ x, (F.neighborSet x).Subsingleton) :
    F.support.ncard = 2 * F.edgeSet.ncard := by
  classical
  obtain ⟨e, he⟩ := matching_support_model F hm
  have hc := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_bool] at hc
  simpa only [← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, Nat.mul_comm] using hc.symm

/-- Finite matching graphs are classified by vertex and edge counts. -/
lemma matching_equiv_of_card {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W)
    (hF : ∀ x, (F.neighborSet x).Subsingleton)
    (hH : ∀ x, (H.neighborSet x).Subsingleton)
    (hv : Fintype.card V = Fintype.card W) (he : F.edgeSet.ncard = H.edgeSet.ncard) :
    ∃ e : V ≃ W, ∀ x y, H.Adj (e x) (e y) ↔ F.Adj x y := by
  classical
  obtain ⟨f, hf⟩ := matching_support_model F hF
  obtain ⟨g, hg⟩ := matching_support_model H hH
  let d : F.edgeSet ≃ H.edgeSet := Fintype.equivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using he)
  let ds := Equiv.prodCongr d (Equiv.refl Bool)
  let es : F.support ≃ H.support := f.symm.trans (ds.trans g)
  have hes (x y : F.support) : H.Adj (es x).val (es y).val ↔ F.Adj x.val y.val := by
    change H.Adj (g (ds (f.symm x))).val (g (ds (f.symm y))).val ↔ F.Adj x.val y.val
    rw [hg]
    have hf' := hf (f.symm x) (f.symm y)
    simpa [ds] using hf'.symm
  have hs : Fintype.card F.support = Fintype.card H.support := Fintype.card_congr es
  let ei : {x : V // x ∉ F.support} ≃ {y : W // y ∉ H.support} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hv, hs])
  let e : V ≃ W := (Equiv.Set.sumCompl F.support).symm.trans
    ((Equiv.sumCongr es ei).trans (Equiv.Set.sumCompl H.support))
  have heS (x : F.support) : e x.val = (es x).val := by
    have hx' : (Equiv.Set.sumCompl F.support).symm x.val = Sum.inl x := by simp
    simp only [e, Equiv.trans_apply, hx', Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inl]
    exact Equiv.Set.sumCompl_apply_inl H.support (es x)
  have heI (x : {x : V // x ∉ F.support}) : e x.val = (ei x).val := by
    have hx' : (Equiv.Set.sumCompl F.support).symm x.val = Sum.inr x := by simp
    simp only [e, Equiv.trans_apply, hx', Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inr]
    exact Equiv.Set.sumCompl_apply_inr H.support (ei x)
  refine ⟨e, ?_⟩
  intro x y
  by_cases hx : x ∈ F.support
  · by_cases hy : y ∈ F.support
    · simpa only [heS ⟨x,hx⟩, heS ⟨y,hy⟩] using hes ⟨x,hx⟩ ⟨y,hy⟩
    · have heY : e y ∉ H.support := (heI ⟨y,hy⟩).symm ▸ (ei ⟨y,hy⟩).property
      exact ⟨fun h ↦ (heY ⟨e x, h.symm⟩).elim, fun h ↦ (hy ⟨x, h.symm⟩).elim⟩
  · have heX : e x ∉ H.support := (heI ⟨x,hx⟩).symm ▸ (ei ⟨x,hx⟩).property
    exact ⟨fun h ↦ (heX ⟨e y, h⟩).elim, fun h ↦ (hx ⟨y, h⟩).elim⟩

/-- Gallai's bound after deleting a matching from an odd-order complete graph. -/
lemma complete_odd_matching_deletion {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hodd : Odd (Fintype.card V))
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card ≤ Fintype.card V + 1 := by
  classical
  obtain ⟨k, hcard⟩ := hodd
  by_cases hk : k = 0
  · have hsmall : Fintype.card V ≤ 1 := by omega
    letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hsmall
    have ht : G.edgeSet = ∅ := by
      ext e
      induction e using Sym2.ind with
      | h x y => simp [Subsingleton.elim x y]
    refine ⟨∅, ⟨by simp, by simp, ?_⟩, by simp⟩
    simp [ht]
  · have hkpos : 0 < k := by omega
    letI : NeZero (2*k) := ⟨by omega⟩
    let t := (Gᶜ).edgeSet.ncard
    have hsupport := matching_support_card Gᶜ hm
    have hle := Set.ncard_le_card (Gᶜ).support
    rw [Nat.card_eq_fintype_card] at hle
    have ht : t ≤ k := by dsimp [t]; omega
    let F := WaleckiCycles.prefixMatching k t
    obtain ⟨e, he⟩ := matching_equiv_of_card F Gᶜ
      (WaleckiCycles.prefixMatching_matching k t) hm
      (by rw [Fintype.card_option, ZMod.card]; omega)
      (WaleckiCycles.prefixMatching_ncard ht)
    have hJ : G.comap e = Fᶜ := by
      ext x y
      rw [comap_adj, compl_adj]
      have hrel := he x y
      rw [compl_adj] at hrel
      constructor
      · intro hxy
        refine ⟨fun h ↦ hxy.ne (congrArg e h), ?_⟩
        intro hF
        exact (hrel.mpr hF).2 hxy
      · rintro ⟨hne, hnF⟩
        by_contra hnG
        exact hnF (hrel.mp ⟨fun h ↦ hne (e.injective h), hnG⟩)
    have hex : ∃ D : Finset (G.comap e).Subgraph,
        GoodDecomposition (G.comap e) D ∧ D.card ≤ k+1 := by
      rw [hJ]
      exact WaleckiCycles.canonical_matching_decomposition k t hkpos ht
    obtain ⟨D, hD, hnD⟩ := hex
    obtain ⟨E, hE, hnE⟩ := GoodDecomposition.map_comap_equiv e hD
    exact ⟨E, hE, by omega⟩

/-- The complement-matching case for every finite vertex type. -/
lemma erdos_583_of_complement_matching {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  rcases Nat.even_or_odd (Fintype.card V) with heven | hodd
  · exact erdos_583_of_even_complement_matching G heven hm
  · obtain ⟨D, hD, hn⟩ := complete_odd_matching_deletion G hodd hm
    have hceil : Fintype.card V ≤ 2 * ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
      have hq := Nat.le_ceil ((Fintype.card V : ℚ) / 2)
      exact_mod_cast (show (Fintype.card V : ℚ) ≤
        2 * (⌈(Fintype.card V : ℚ) / 2⌉₊ : ℚ) by linarith)
    exact ⟨D, hD, by omega⟩

end Erdos583CycleDevelopment
