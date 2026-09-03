import Submission.Work

/-! Walecki's explicit decomposition of finite complete graphs. -/

open SimpleGraph Erdos583Work
namespace Erdos583WaleckiDevelopment
namespace Walecki

def zig (n j : ℕ) : ℕ := if j % 2 = 0 then j / 2 else n - (j+1)/2

lemma zig_lt {k j : ℕ} (hj : j < 2*k) : zig (2*k) j < 2*k := by
  unfold zig
  split_ifs <;> omega

lemma zig_injective {k i j : ℕ} (hi : i < 2*k) (hj : j < 2*k)
    (he : zig (2*k) i = zig (2*k) j) : i = j := by
  unfold zig at he
  split_ifs at he <;> omega

lemma zig_succ_sum {k j : ℕ} (hj : j + 1 < 2*k) :
    zig (2*k) j + zig (2*k) (j+1) + 1 = 2*k + (if j%2=0 then 0 else 1) := by
  unfold zig
  split_ifs <;> omega

def vertex {k : ℕ} (i : Fin k) (j : Fin (2*k)) : ZMod (2*k) :=
  (i.val : ZMod (2*k)) + (zig (2*k) j.val : ℕ)

lemma vertex_injective {k : ℕ} (i : Fin k) : Function.Injective (vertex i) := by
  intro a b hab
  have he : (zig (2*k) a.val : ZMod (2*k)) = (zig (2*k) b.val : ZMod (2*k)) :=
    add_left_cancel hab
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (zig_lt a.isLt), ZMod.val_natCast_of_lt (zig_lt b.isLt)] at hv
  exact Fin.ext (zig_injective a.isLt b.isLt hv)

lemma vertex_color {k : ℕ} (i : Fin k) {j : ℕ} (hj : j+1 < 2*k) :
    (vertex i ⟨j, by omega⟩ + vertex i ⟨j+1, hj⟩ + 1).val / 2 = i.val := by
  have hs := zig_succ_sum hj
  have he : vertex i ⟨j, by omega⟩ + vertex i ⟨j+1, hj⟩ + 1 =
      ((2*i.val + (if j%2=0 then 0 else 1) : ℕ) : ZMod (2*k)) := by
    have hc := congrArg (fun x : ℕ ↦ (x : ZMod (2*k))) hs
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] at hc
    simp only [vertex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linear_combination hc
  rw [he, ZMod.val_natCast_of_lt (by have := i.isLt; split_ifs <;> omega)]
  split_ifs <;> omega

lemma exists_walk_support {V : Type*} {G : SimpleGraph V} (a : V) (l : List V)
    (h : List.IsChain G.Adj (a::l)) : ∃ b, ∃ p : G.Walk a b, p.support = a::l := by
  induction l generalizing a with
  | nil => exact ⟨a, .nil, rfl⟩
  | cons b l ih =>
    obtain ⟨c, p, hp⟩ := ih b h.tail
    exact ⟨c, .cons (List.isChain_cons_cons.mp h).1 p, by simp [hp]⟩

lemma exists_path_support {V : Type*} {G : SimpleGraph V} {l : List V}
    (hne : l ≠ []) (hn : l.Nodup) (hc : l.IsChain G.Adj) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.support = l := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l =>
    obtain ⟨b, p, hp⟩ := exists_walk_support a l hc
    exact ⟨a, b, p, Walk.IsPath.mk' (hp.symm ▸ hn), hp⟩

lemma exists_path_vertex {k : ℕ} (i : Fin k) :
    ∃ a b, ∃ p : (⊤ : SimpleGraph (ZMod (2*k))).Walk a b,
      p.IsPath ∧ p.support = List.ofFn (vertex i) := by
  apply exists_path_support
  · intro h
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at this
    have := i.isLt
    omega
  · exact List.nodup_ofFn_ofInjective (vertex_injective i)
  · rw [List.isChain_ofFn]
    intro j hj he
    have hval : j = j+1 := congrArg Fin.val (vertex_injective i he)
    omega

lemma mem_edges_index {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ j, j < p.length ∧ e = s(p.getVert j, p.getVert (j+1)) := by
  induction p with
  | nil => simp at he
  | cons h q ih =>
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨j, hj, he⟩ := ih he
      exact ⟨j+1, by simpa using hj, by simpa using he⟩

lemma getVert_of_support_eq_ofFn {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {n : ℕ} {f : Fin n → V} (hs : p.support = List.ofFn f)
    (j : ℕ) (hj : j < n) : p.getVert j = f ⟨j, hj⟩ := by
  have hl : p.length + 1 = n := by simpa using congrArg List.length hs
  have he := p.getVert_eq_support_getElem (n := j) (by omega)
  simpa only [hs, List.getElem_ofFn] using he

lemma path_vertex_color {k : ℕ} (i : Fin k) {a b : ZMod (2*k)}
    (p : (⊤ : SimpleGraph (ZMod (2*k))).Walk a b)
    (hs : p.support = List.ofFn (vertex i)) {x y : ZMod (2*k)}
    (he : s(x,y) ∈ p.edges) : (x+y+1).val/2 = i.val := by
  have hl : p.length + 1 = 2*k := by simpa using congrArg List.length hs
  obtain ⟨j, hj, he⟩ := mem_edges_index p he
  rw [getVert_of_support_eq_ofFn p hs j (by omega),
    getVert_of_support_eq_ofFn p hs (j+1) (by omega)] at he
  have hc := vertex_color i (j := j) (by omega)
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hc
  · simpa only [add_comm (vertex i ⟨j, by omega⟩) (vertex i ⟨j+1, by omega⟩)] using hc


lemma decomposition_of_family_of_card {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (f : I → G.Subgraph)
    (hf : ∀ i, IsPathSubgraph (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet))
    (hc : ∑ i, (f i).edgeSet.ncard = G.edgeSet.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ Fintype.card I := by
  classical
  let U := ⋃ i, (f i).edgeSet
  have hsub : U ⊆ G.edgeSet := by
    rintro e ⟨_, ⟨i, rfl⟩, he⟩
    exact (f i).edgeSet_subset he
  have hcard : U.ncard = G.edgeSet.ncard := by
    have hU : U = ⋃ i ∈ ((Finset.univ : Finset I) : Set I), (f i).edgeSet := by simp [U]
    rw [hU]
    rw [(Finset.univ : Finset I).finite_toSet.ncard_biUnion
      (fun _ _ ↦ Set.toFinite _) (fun i _ j _ hij ↦ hd hij), finsum_mem_coe_finset]
    exact hc
  have hcover : U = G.edgeSet := Set.eq_of_subset_of_ncard_le hsub hcard.ge
  let D := Finset.univ.image f
  refine ⟨D, ⟨?_, ?_, ?_⟩, Finset.card_image_le.trans (by simp)⟩
  · intro K hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hK
    exact hf i
  · intro K hK L hL hKL
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hL
    exact hd (fun hij ↦ hKL (congrArg f hij))
  · simpa [D, U] using hcover

lemma complete_even_decomposition (k : ℕ) (hk : 0 < k) :
    ∃ D : Finset (⊤ : SimpleGraph (ZMod (2*k))).Subgraph,
      GoodDecomposition ⊤ D ∧ D.card ≤ k := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  choose a b p hp hs using exists_path_vertex (k := k)
  have hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with
    | h x y =>
      have hci := path_vertex_color i (p i) (hs i) ((p i).mem_edges_toSubgraph.mp hei)
      have hcj := path_vertex_color j (p j) (hs j) ((p j).mem_edges_toSubgraph.mp hej)
      exact hij (Fin.ext (hci.symm.trans hcj))
  have hc (i : Fin k) : (p i).toSubgraph.edgeSet.ncard = 2*k-1 := by
    rw [path_edgeSet_ncard (hp i)]
    have hl := congrArg List.length (hs i)
    simp only [Walk.length_support, List.length_ofFn] at hl
    omega
  have ht : (⊤ : SimpleGraph (ZMod (2*k))).edgeSet.ncard = k*(2*k-1) := by
    rw [Set.ncard_eq_toFinset_card']
    change (⊤ : SimpleGraph (ZMod (2*k))).edgeFinset.card = _
    rw [card_edgeFinset_top_eq_card_choose_two, ZMod.card, Nat.choose_two_right]
    simp [Nat.mul_assoc]
  obtain ⟨D, hD, hn⟩ := decomposition_of_family_of_card
    (⊤ : SimpleGraph (ZMod (2*k))) (fun i ↦ (p i).toSubgraph)
    (fun i ↦ ⟨a i, b i, p i, hp i, rfl⟩) hd (by
      simp only [hc, ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id])
  exact ⟨D, hD, by simpa using hn⟩


lemma vertex_zero {k : ℕ} (i : Fin k) (h : 0 < 2*k) :
    vertex i ⟨0, h⟩ = (i.val : ZMod (2*k)) := by simp [vertex, zig]

lemma vertex_one {k : ℕ} (i : Fin k) (h : 1 < 2*k) :
    vertex i ⟨1, h⟩ = (i.val : ZMod (2*k)) - 1 := by
  simp [vertex, zig, Nat.cast_sub (by omega : 1 ≤ 2*k), sub_eq_add_neg]

lemma vertex_last {k : ℕ} (i : Fin k) (h : 2*k-1 < 2*k) :
    vertex i ⟨2*k-1, h⟩ = (i.val : ZMod (2*k)) + (k : ZMod (2*k)) := by
  have hz : zig (2*k) (2*k-1) = k := by unfold zig; split_ifs <;> omega
  simp [vertex, hz]

lemma exists_tail {k : ℕ} (i : Fin k) :
    ∃ q : (⊤ : SimpleGraph (ZMod (2*k))).Walk
      ((i.val : ZMod (2*k))-1) ((i.val : ZMod (2*k)) + k),
      q.IsPath ∧ (i.val : ZMod (2*k)) ∉ q.support ∧
      s((i.val : ZMod (2*k)), (i.val : ZMod (2*k))-1) ∉ q.edges ∧
      q.length = 2*k-2 ∧
      ∀ x y, s(x,y) ∈ q.edges → (x+y+1).val/2 = i.val := by
  obtain ⟨a, b, p, hp, hs⟩ := exists_path_vertex i
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hl : p.length + 1 = 2*k := by simpa using congrArg List.length hs
  have ha : a = (i.val : ZMod (2*k)) := by
    calc
      a = vertex i ⟨0, by omega⟩ := by
        simpa only [Walk.getVert_zero] using getVert_of_support_eq_ofFn p hs 0 (by omega)
      _ = _ := vertex_zero i _
  have hb : b = (i.val : ZMod (2*k)) + k := by
    have hv := getVert_of_support_eq_ofFn p hs p.length (by omega)
    rw [Walk.getVert_length] at hv
    have hv' : p.length = 2*k-1 := by omega
    simpa only [hv', vertex_last] using hv
  cases p with
  | nil => simp only [Walk.length_nil] at hl; omega
  | @cons a x b h q =>
    subst a b
    have hx : x = (i.val : ZMod (2*k))-1 := by
      calc
        x = vertex i ⟨1, by omega⟩ := by
          simpa only [Walk.getVert_cons_succ, Walk.getVert_zero] using
            getVert_of_support_eq_ofFn (.cons h q) hs 1 (by omega)
        _ = _ := vertex_one i _
    subst x
    refine ⟨q, hp.of_cons, ?_, ?_, ?_, ?_⟩
    · exact (List.nodup_cons.mp hp.support_nodup).1
    · exact (Walk.isTrail_cons h q).mp hp.isTrail |>.2
    · simp only [Walk.length_cons] at hl
      omega
    · intro x y he
      exact path_vertex_color i (.cons h q) hs (by simp [he])

def someHom (V : Type*) : (⊤ : SimpleGraph V) →g (⊤ : SimpleGraph (Option V)) where
  toFun := some
  map_rel' := by intro a b h he; exact h (Option.some.inj he)

def liftTail {V : Type*} {x y : V} (z : V) (q : (⊤ : SimpleGraph V).Walk x y) :
    (⊤ : SimpleGraph (Option V)).Walk (some z) (some x) :=
  .cons (by simp : (⊤ : SimpleGraph (Option V)).Adj (some z) none)
    (.cons (by simp : (⊤ : SimpleGraph (Option V)).Adj none (some y))
      (q.reverse.map (someHom V)))

lemma liftTail_isPath {V : Type*} {x y : V} (z : V)
    (q : (⊤ : SimpleGraph V).Walk x y) (hq : q.IsPath) (hz : z ∉ q.support) :
    (liftTail z q).IsPath := by
  unfold liftTail
  apply Walk.IsPath.cons
  · apply Walk.IsPath.cons
    · exact Walk.map_isPath_of_injective (Option.some_injective V) hq.reverse
    · simp [Walk.support_map, someHom]
  · simp [Walk.support_map, someHom, hz]

lemma liftTail_length {V : Type*} {x y : V} (z : V)
    (q : (⊤ : SimpleGraph V).Walk x y) : (liftTail z q).length = q.length + 2 := by
  simp [liftTail]

lemma liftTail_mem_edges {V : Type*} {x y : V} (z : V)
    (q : (⊤ : SimpleGraph V).Walk x y) (e : Sym2 (Option V)) :
    e ∈ (liftTail z q).edges ↔ e = s(some z, none) ∨ e = s(some y, none) ∨
      ∃ e' ∈ q.edges, Sym2.map some e' = e := by
  simp [liftTail, Walk.edges_map, someHom, Sym2.eq_swap]

lemma endpoint_index {k : ℕ} (i j : Fin k) (b c : Bool)
    (he : ((i.val + (if b then k else 0) : ℕ) : ZMod (2*k)) =
      ((j.val + (if c then k else 0) : ℕ) : ZMod (2*k))) : i = j := by
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (by split_ifs <;> omega),
    ZMod.val_natCast_of_lt (by split_ifs <;> omega)] at hv
  exact Fin.ext (by split_ifs at hv <;> omega)


lemma map_some_ne_spoke {V : Type*} (e : Sym2 V) (x : V) :
    Sym2.map some e ≠ s(some x, none) := by
  induction e using Sym2.ind with
  | h a b => simp

lemma liftTail_finite_mem_edges {V : Type*} {x y : V} (z : V)
    (q : (⊤ : SimpleGraph V).Walk x y) (a b : V) :
    s(some a, some b) ∈ (liftTail z q).edges ↔ s(a,b) ∈ q.edges := by
  rw [liftTail_mem_edges]
  have hz : s(some a, some b) ≠ s(some z, none) := map_some_ne_spoke s(a,b) z
  have hy : s(some a, some b) ≠ s(some y, none) := map_some_ne_spoke s(a,b) y
  simp only [hz, hy, false_or]
  constructor
  · rintro ⟨e, he, heq⟩
    have : e = s(a,b) := (Sym2.map.injective (Option.some_injective V)) heq
    simpa [this] using he
  · intro he
    exact ⟨s(a,b), he, rfl⟩

lemma liftTail_spoke_mem_edges {V : Type*} {x y : V} (z : V)
    (q : (⊤ : SimpleGraph V).Walk x y) (a : V) :
    s(some a, none) ∈ (liftTail z q).edges ↔ a = z ∨ a = y := by
  rw [liftTail_mem_edges]
  have hm : ¬∃ e' ∈ q.edges, Sym2.map some e' = s(some a, none) := by
    rintro ⟨e', _, he⟩
    exact map_some_ne_spoke e' a he
  simp [hm]

lemma first_color {k : ℕ} (i : Fin k) :
    ((i.val : ZMod (2*k)) + ((i.val : ZMod (2*k))-1) + 1).val/2 = i.val := by
  have he : (i.val : ZMod (2*k)) + ((i.val : ZMod (2*k))-1) + 1 =
      ((2*i.val : ℕ) : ZMod (2*k)) := by push_cast; ring
  rw [he, ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
  omega

def shortVertex {k : ℕ} (j : Fin (k+1)) : ZMod (2*k) := (j.val : ZMod (2*k))-1

lemma shortVertex_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (shortVertex (k := k)) := by
  intro i j he
  have hc : (i.val : ZMod (2*k)) = (j.val : ZMod (2*k)) := sub_left_inj.mp he
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega),
    ZMod.val_natCast_of_lt (by have := j.isLt; omega)] at hv
  exact Fin.ext hv

lemma exists_short_path (k : ℕ) (hk : 0 < k) :
    ∃ a b, ∃ p : (⊤ : SimpleGraph (ZMod (2*k))).Walk a b,
      p.IsPath ∧ p.length = k ∧ ∀ e ∈ p.edges,
        ∃ i : Fin k, e = s((i.val : ZMod (2*k)), (i.val : ZMod (2*k))-1) := by
  have hne : List.ofFn (shortVertex (k := k)) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hc : (List.ofFn (shortVertex (k := k))).IsChain
      (⊤ : SimpleGraph (ZMod (2*k))).Adj := by
    rw [List.isChain_ofFn]
    intro j hj he
    have hval : j = j+1 := congrArg Fin.val (shortVertex_injective hk he)
    omega
  obtain ⟨a, b, p, hp, hs⟩ := exists_path_support hne
    (List.nodup_ofFn_ofInjective (shortVertex_injective hk)) hc
  have hl : p.length = k := by
    have := congrArg List.length hs
    simpa using this
  refine ⟨a, b, p, hp, hl, ?_⟩
  intro e he
  obtain ⟨j, hj, he⟩ := mem_edges_index p he
  rw [hl] at hj
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [getVert_of_support_eq_ofFn p hs j (by omega),
    getVert_of_support_eq_ofFn p hs (j+1) (by omega)] at he
  simpa only [shortVertex, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Sym2.eq_swap] using he


lemma complete_odd_decomposition (k : ℕ) (hk : 0 < k) :
    ∃ D : Finset (⊤ : SimpleGraph (Option (ZMod (2*k)))).Subgraph,
      GoodDecomposition ⊤ D ∧ D.card ≤ k+1 := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  choose q hq hz he hlen hcolor using exists_tail (k := k)
  let r (i : Fin k) := liftTail (i.val : ZMod (2*k)) (q i)
  have hr (i : Fin k) : (r i).IsPath := liftTail_isPath _ _ (hq i) (hz i)
  have hrL (i : Fin k) : (r i).length = 2*k := by
    dsimp only [r]
    rw [liftTail_length, hlen i]
    omega
  have hdr : Pairwise (fun i j ↦ Disjoint (r i).toSubgraph.edgeSet (r j).toSubgraph.edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    have hei' := (r i).mem_edges_toSubgraph.mp hei
    have hej' := (r j).mem_edges_toSubgraph.mp hej
    rcases (liftTail_mem_edges _ (q i) e).mp hei' with rfl | rfl | ⟨e', he', rfl⟩
    · apply hij
      rcases (liftTail_spoke_mem_edges _ (q j) _).mp hej' with h | h
      · exact endpoint_index i j false false (by simpa using h)
      · exact endpoint_index i j false true (by simpa using h)
    · apply hij
      rcases (liftTail_spoke_mem_edges _ (q j) _).mp hej' with h | h
      · exact endpoint_index i j true false (by simpa using h)
      · exact endpoint_index i j true true (by simpa using h)
    · induction e' using Sym2.ind with
      | h x y =>
        have hjq := (liftTail_finite_mem_edges _ (q j) x y).mp hej'
        exact hij (Fin.ext ((hcolor i x y he').symm.trans (hcolor j x y hjq)))
  obtain ⟨a, b, p, hp, hpL, hpe⟩ := exists_short_path k hk
  let p₀ := p.map (someHom (ZMod (2*k)))
  have hp₀ : p₀.IsPath := Walk.map_isPath_of_injective (Option.some_injective _) hp
  have hd₀ (i : Fin k) : Disjoint p₀.toSubgraph.edgeSet (r i).toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hep her
    have hep' : e ∈ p.edges.map (Sym2.map (someHom (ZMod (2*k)))) := by
      simpa only [p₀, Walk.edges_map] using p₀.mem_edges_toSubgraph.mp hep
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hep'
    obtain ⟨j, rfl⟩ := hpe e' he'
    have hrq := (liftTail_finite_mem_edges _ (q i) (j.val : ZMod (2*k))
      ((j.val : ZMod (2*k))-1)).mp ((r i).mem_edges_toSubgraph.mp her)
    have hij : i = j := Fin.ext ((hcolor i _ _ hrq).symm.trans (first_color j))
    subst j
    exact he i hrq
  let f : Option (Fin k) → (⊤ : SimpleGraph (Option (ZMod (2*k)))).Subgraph
    | none => p₀.toSubgraph
    | some i => (r i).toSubgraph
  have hf (i : Option (Fin k)) : IsPathSubgraph (f i) := by
    cases i with
    | none => exact ⟨some a, some b, p₀, hp₀, rfl⟩
    | some i => exact ⟨_, _, r i, hr i, rfl⟩
  have hd : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hd₀ j
    | some i =>
      cases j with
      | none => exact (hd₀ i).symm
      | some j => exact hdr (fun h ↦ hij (congrArg some h))
  have hc₀ : p₀.toSubgraph.edgeSet.ncard = k := by
    rw [path_edgeSet_ncard hp₀]
    simpa [p₀] using hpL
  have hci (i : Fin k) : (r i).toSubgraph.edgeSet.ncard = 2*k := by
    rw [path_edgeSet_ncard (hr i), hrL i]
  have ht : (⊤ : SimpleGraph (Option (ZMod (2*k)))).edgeSet.ncard = k*(2*k+1) := by
    rw [Set.ncard_eq_toFinset_card']
    change (⊤ : SimpleGraph (Option (ZMod (2*k)))).edgeFinset.card = _
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_option, ZMod.card,
      Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_comm (2*k+1), Nat.mul_assoc]
    simp
  obtain ⟨D, hD, hn⟩ := decomposition_of_family_of_card
    (⊤ : SimpleGraph (Option (ZMod (2*k)))) f hf hd (by
      simp only [Fintype.sum_option, f, hc₀, hci, ht, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring)
  exact ⟨D, hD, by simpa using hn⟩


lemma complete_transfer {V W : Type*} (e : V ≃ W)
    {D : Finset (⊤ : SimpleGraph V).Subgraph} (hD : GoodDecomposition ⊤ D) :
    ∃ E : Finset (⊤ : SimpleGraph W).Subgraph,
      GoodDecomposition ⊤ E ∧ E.card ≤ D.card := by
  let f : (⊤ : SimpleGraph V) →g (⊤ : SimpleGraph W) :=
    ⟨e, fun h he ↦ h (e.injective he)⟩
  apply hD.map_of_edge_surjective f e.injective
  ext d
  induction d using Sym2.ind with
  | h a b =>
    constructor
    · intro hab
      refine ⟨s(e.symm a, e.symm b), ?_, ?_⟩
      · exact fun h ↦ hab (by simpa using congrArg e h)
      · simp [f]
    · rintro ⟨d, hd, he⟩
      induction d using Sym2.ind with
      | h x y =>
        have hxy : (⊤ : SimpleGraph W).Adj (e x) (e y) := fun h ↦ hd (e.injective h)
        exact ((⊤ : SimpleGraph W).adj_congr_of_sym2 he).mp hxy

lemma complete_decomposition {V : Type*} [Fintype V] :
    ∃ D : Finset (⊤ : SimpleGraph V).Subgraph,
      GoodDecomposition ⊤ D ∧ 2*D.card ≤ Fintype.card V + 1 := by
  classical
  by_cases hn : Fintype.card V ≤ 1
  · letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn
    have ht : (⊤ : SimpleGraph V).edgeSet = ∅ := by
      ext e
      induction e using Sym2.ind with
      | h a b => simp [Subsingleton.elim a b]
    refine ⟨∅, ⟨by simp, ?_, ?_⟩, by simp⟩
    · simp
    · simp [ht]
  · let k := Fintype.card V / 2
    have hk : 0 < k := by dsimp [k]; omega
    letI : NeZero (2*k) := ⟨by omega⟩
    have hn' : 2*k + Fintype.card V % 2 = Fintype.card V := Nat.div_add_mod _ _
    by_cases hp : Fintype.card V % 2 = 0
    · obtain ⟨D, hD, hDc⟩ := complete_even_decomposition k hk
      let e : ZMod (2*k) ≃ V := Fintype.equivOfCardEq (by rw [ZMod.card]; omega)
      obtain ⟨E, hE, hEc⟩ := complete_transfer e hD
      exact ⟨E, hE, by omega⟩
    · have hp' : Fintype.card V % 2 = 1 := by omega
      obtain ⟨D, hD, hDc⟩ := complete_odd_decomposition k hk
      let e : Option (ZMod (2*k)) ≃ V := Fintype.equivOfCardEq
        (by rw [Fintype.card_option, ZMod.card]; omega)
      obtain ⟨E, hE, hEc⟩ := complete_transfer e hD
      exact ⟨E, hE, by omega⟩


end Walecki
/-- Walecki's construction gives the conjectured bound for all complete graphs. -/
lemma complete_erdos_583 {V : Type*} [Fintype V] :
    ∃ D : Finset (⊤ : SimpleGraph V).Subgraph,
      GoodDecomposition ⊤ D ∧ D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  obtain ⟨D, hD, hc⟩ := Walecki.complete_decomposition (V := V)
  have hceil : Fintype.card V ≤ 2 * ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
    have hq := Nat.le_ceil ((Fintype.card V : ℚ) / 2)
    exact_mod_cast (show (Fintype.card V : ℚ) ≤
      2 * (⌈(Fintype.card V : ℚ) / 2⌉₊ : ℚ) by linarith)
  exact ⟨D, hD, by omega⟩

end Erdos583WaleckiDevelopment
