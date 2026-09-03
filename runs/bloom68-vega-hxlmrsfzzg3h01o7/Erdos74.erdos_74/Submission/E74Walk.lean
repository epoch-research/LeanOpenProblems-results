import Submission.E74Basic

/-!
# Bounded walks, edge supports, and elementary coloring utilities

All neighborhood statements use `E74.Near`, hence require an actual walk even
between vertices in different connected components.  No numerical graph distance
or parity argument is used here.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V]

/-! ## Endpoints of finite edge sets -/

theorem mem_ends_of_mem {E : Finset (Sym2 V)} {e : Sym2 V} {v : V}
    (he : e ∈ E) (hv : v ∈ e) : v ∈ ends E :=
  mem_ends.mpr ⟨e, he, hv⟩

theorem mem_ends_left {E : Finset (Sym2 V)} {u v : V}
    (h : s(u, v) ∈ E) : u ∈ ends E :=
  mem_ends_of_mem h (Sym2.mem_mk_left u v)

theorem mem_ends_right {E : Finset (Sym2 V)} {u v : V}
    (h : s(u, v) ∈ E) : v ∈ ends E :=
  mem_ends_of_mem h (Sym2.mem_mk_right u v)

theorem ends_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) : ends E ⊆ ends F := by
  intro v hv
  rcases mem_ends.mp hv with ⟨e, he, hve⟩
  exact mem_ends_of_mem (h he) hve

@[simp] theorem ends_singleton (e : Sym2 V) : ends {e} = e.toFinset := by
  classical
  simp [ends]

theorem ends_subset_iff {E : Finset (Sym2 V)} {W : Set V} :
    (ends E : Set V) ⊆ W ↔ ∀ e ∈ E, ∀ v ∈ e, v ∈ W := by
  constructor
  · intro h e he v hv
    exact h (mem_ends_of_mem he hv)
  · intro h v hv
    rcases mem_ends.mp hv with ⟨e, he, hve⟩
    exact h e he v hve

theorem pair_not_mem_of_left_not_mem_ends {E : Finset (Sym2 V)} {u v : V}
    (h : u ∉ ends E) : s(u, v) ∉ E :=
  fun he => h (mem_ends_left he)

theorem pair_not_mem_of_right_not_mem_ends {E : Finset (Sym2 V)} {u v : V}
    (h : v ∉ ends E) : s(u, v) ∉ E :=
  fun he => h (mem_ends_right he)

/-! ## Bounded reachability -/

variable {G H : SimpleGraph V} {X Y : Set V} {a b r s : ℕ} {u v x : V}

section BoundedReachability
omit [DecidableEq V]

theorem near_of_mem (hv : v ∈ X) : Near G X r v :=
  ⟨v, hv, Walk.nil, Nat.zero_le r⟩

@[simp] theorem near_zero : Near G X 0 v ↔ v ∈ X := by
  constructor
  · rintro ⟨x, hx, w, hw⟩
    exact (w.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hw)).symm ▸ hx
  · exact near_of_mem

@[simp] theorem not_near_empty : ¬ Near G (∅ : Set V) r v := by
  simp [Near]

@[simp] theorem near_univ : Near G Set.univ r v :=
  near_of_mem (Set.mem_univ v)

theorem near_mono_radius (hrs : r ≤ s) (hv : Near G X r v) : Near G X s v := by
  rcases hv with ⟨x, hx, w, hw⟩
  exact ⟨x, hx, w, hw.trans hrs⟩

theorem near_mono_set (hXY : X ⊆ Y) (hv : Near G X r v) : Near G Y r v := by
  rcases hv with ⟨x, hx, w, hw⟩
  exact ⟨x, hXY hx, w, hw⟩

theorem near_mono_graph (hGH : G ≤ H) (hv : Near G X r v) : Near H X r v := by
  rcases hv with ⟨x, hx, w, hw⟩
  exact ⟨x, hx, w.mapLe hGH, by simpa using hw⟩

theorem near_mono (hGH : G ≤ H) (hXY : X ⊆ Y) (hrs : r ≤ s)
    (hv : Near G X r v) : Near H Y s v :=
  near_mono_graph hGH (near_mono_set hXY (near_mono_radius hrs hv))

theorem near_of_walk (w : G.Walk v x) (hx : x ∈ X) : Near G X w.length v :=
  ⟨x, hx, w, le_rfl⟩

/-- Compose bounded walks through a set of intermediate vertices. -/
theorem near_trans (hv : Near G Y a v) (hY : ∀ y ∈ Y, Near G X b y) :
    Near G X (a + b) v := by
  rcases hv with ⟨y, hy, w, hw⟩
  rcases hY y hy with ⟨x, hx, q, hq⟩
  exact ⟨x, hx, w.append q, by simpa using Nat.add_le_add hw hq⟩

theorem near_prepend (huv : G.Adj u v) (hv : Near G X r v) :
    Near G X (r + 1) u := by
  rcases hv with ⟨x, hx, w, hw⟩
  exact ⟨x, hx, w.cons huv, by simpa using Nat.add_le_add_right hw 1⟩

theorem near_of_adj (huv : G.Adj u v) (hv : v ∈ X) : Near G X 1 u :=
  near_prepend huv (near_of_mem (r := 0) hv)

theorem near_prepend_walk (w : G.Walk u v) (hv : Near G X r v) :
    Near G X (w.length + r) u := by
  rcases hv with ⟨x, hx, q, hq⟩
  exact ⟨x, hx, w.append q, by simpa using Nat.add_le_add_left hq w.length⟩

/-- Moving the starting vertex along a walk costs at most the walk's length. -/
theorem near_along_walk (hu : Near G X r u) (w : G.Walk u v) :
    Near G X (r + w.length) v := by
  simpa [Nat.add_comm] using near_prepend_walk w.reverse hu

@[simp] theorem near_singleton_iff :
    Near G {x} r v ↔ ∃ w : G.Walk v x, w.length ≤ r := by
  simp [Near]

theorem near_singleton_symm : Near G {u} r v ↔ Near G {v} r u := by
  simp only [near_singleton_iff]
  constructor <;> rintro ⟨w, hw⟩ <;> exact ⟨w.reverse, by simpa using hw⟩

theorem near_singleton_trans (huv : Near G {v} a u) (hvx : Near G {x} b v) :
    Near G {x} (a + b) u := by
  apply near_trans huv
  intro y hy
  simpa only [Set.mem_singleton_iff.mp hy] using hvx

theorem near_iff_exists_singleton :
    Near G X r v ↔ ∃ x ∈ X, Near G {x} r v := by
  simp [Near]

@[simp] theorem near_union : Near G (X ∪ Y) r v ↔ Near G X r v ∨ Near G Y r v := by
  simp [Near, or_and_right, exists_or]

theorem near_succ_iff :
    Near G X (r + 1) v ↔ v ∈ X ∨ ∃ u, G.Adj v u ∧ Near G X r u := by
  constructor
  · rintro ⟨x, hx, w, hw⟩
    cases w with
    | nil => exact Or.inl hx
    | cons h w =>
      exact Or.inr ⟨_, h, _, hx, w, by simpa using hw⟩
  · rintro (hv | ⟨u, hvu, hu⟩)
    · exact near_of_mem hv
    · exact near_prepend hvu hu

end BoundedReachability

/-! ## First-hit invariance under edge deletion -/

/-- Stop a walk at its first vertex in `W`.  Every edge before that first hit
survives deletion, since all endpoints of the deleted edges lie in `W`. -/
theorem near_deleteEdges_of_walk {U : Finset (Sym2 V)} {W : Set V}
    (hU : (ends U : Set V) ⊆ W) (w : G.Walk v x) (hx : x ∈ W) :
    Near (G.deleteEdges (U : Set (Sym2 V))) W w.length v := by
  classical
  induction w with
  | nil => exact near_of_mem hx
  | @cons u v x huv w ih =>
    by_cases hu : u ∈ W
    · exact near_of_mem hu
    · have he : s(u, v) ∉ U := fun he => hu (hU (mem_ends_left he))
      have hadj : (G.deleteEdges (U : Set (Sym2 V))).Adj u v :=
        SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
      simpa only [Walk.length_cons] using near_prepend hadj (ih hx)

/-- Deleting edges whose endpoints are in the target does not change bounded
reachability to that target, including for disconnected graphs. -/
theorem near_deleteEdges_iff {U : Finset (Sym2 V)} {W : Set V}
    (hU : (ends U : Set V) ⊆ W) :
    Near (G.deleteEdges (U : Set (Sym2 V))) W r v ↔ Near G W r v := by
  constructor
  · exact near_mono_graph (G.deleteEdges_le _)
  · rintro ⟨x, hx, w, hw⟩
    exact near_mono_radius hw (near_deleteEdges_of_walk hU w hx)

theorem near_deleteEdges_iff_of_endpoints {U : Finset (Sym2 V)} {W : Set V}
    (hU : ∀ e ∈ U, ∀ x ∈ e, x ∈ W) :
    Near (G.deleteEdges (U : Set (Sym2 V))) W r v ↔ Near G W r v :=
  near_deleteEdges_iff (ends_subset_iff.mpr hU)

@[simp] theorem near_deleteEdges_ends_iff (G : SimpleGraph V) (U : Finset (Sym2 V))
    (r : ℕ) (v : V) :
    Near (G.deleteEdges (U : Set (Sym2 V))) (ends U : Set V) r v ↔
      Near G (ends U : Set V) r v :=
  near_deleteEdges_iff (Set.Subset.refl _)

/-! ## Bad edges -/

section BadGraphs
omit [DecidableEq V]

theorem badGraph_le (G : SimpleGraph V) (p : V → Bool) : badGraph G p ≤ G :=
  fun _ _ h => h.1

theorem badGraph_mono (hGH : G ≤ H) (p : V → Bool) : badGraph G p ≤ badGraph H p :=
  fun _ _ h => ⟨hGH h.1, h.2⟩

end BadGraphs

section FiniteBadEdges
variable [Fintype V]

theorem badEdges_subset_edgeSet (G : SimpleGraph V) (p : V → Bool) :
    (badEdges G p : Set (Sym2 V)) ⊆ G.edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v => exact ((mem_badEdges G p u v).mp he).1

theorem badEdges_mono (hGH : G ≤ H) (p : V → Bool) : badEdges G p ⊆ badEdges H p := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    rcases (mem_badEdges G p u v).mp he with ⟨huv, hp⟩
    exact (mem_badEdges H p u v).mpr ⟨hGH huv, hp⟩

theorem badEdges_mask_subset (G : SimpleGraph V) (Z : Set V) (p : V → Bool) :
    badEdges (mask G Z) p ⊆ badEdges G p :=
  badEdges_mono (mask_le G Z) p

/-- Equality of bad-edge supports can be checked on unordered pairs. -/
theorem badEdges_eq_iff (G : SimpleGraph V) (p : V → Bool) (S : Finset (Sym2 V)) :
    badEdges G p = S ↔ ∀ u v, (G.Adj u v ∧ p u = p v ↔ s(u, v) ∈ S) := by
  constructor
  · intro h u v
    rw [← h, mem_badEdges]
  · intro hS
    ext e
    induction e using Sym2.inductionOn with
    | hf u v => exact (mem_badEdges G p u v).trans (hS u v)

/-- If `S` consists of graph edges, only adjacent pairs need to be checked. -/
theorem badEdges_eq_iff_of_subset {p : V → Bool} {S : Finset (Sym2 V)}
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet) :
    badEdges G p = S ↔ ∀ u v, G.Adj u v → (p u = p v ↔ s(u, v) ∈ S) := by
  constructor
  · intro h u v huv
    simp only [← h, mem_badEdges, huv, true_and]
  · intro hp
    apply (badEdges_eq_iff G p S).mpr
    intro u v
    constructor
    · rintro ⟨huv, heq⟩
      exact (hp u v huv).mp heq
    · intro he
      have huv : G.Adj u v := hS he
      exact ⟨huv, (hp u v huv).mpr he⟩

theorem badEdges_eq_of_adj_iff {p : V → Bool} {S : Finset (Sym2 V)}
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet)
    (hp : ∀ u v, G.Adj u v → (p u = p v ↔ s(u, v) ∈ S)) : badEdges G p = S :=
  (badEdges_eq_iff_of_subset hS).mpr hp

@[simp] theorem badEdges_eq_empty_iff (G : SimpleGraph V) (p : V → Bool) :
    badEdges G p = ∅ ↔ ∀ ⦃u v⦄, G.Adj u v → p u ≠ p v := by
  simp [badEdges_eq_iff]

@[simp] theorem badEdges_mask_eq_empty_iff (G : SimpleGraph V) (Z : Set V) (p : V → Bool) :
    badEdges (mask G Z) p = ∅ ↔ ProperOff G Z p := by
  simp only [badEdges_eq_empty_iff, mask_adj, and_imp, ProperOff]

/-- Removing all endpoints of bad edges leaves the given Boolean assignment proper. -/
theorem properOff_ends_badEdges (G : SimpleGraph V) (p : V → Bool) :
    ProperOff G (ends (badEdges G p) : Set V) p := by
  intro u v huv hu _ heq
  exact hu (mem_ends_left ((mem_badEdges G p u v).mpr ⟨huv, heq⟩))

end FiniteBadEdges

/-! ## Downward heredity of the small-cut hypothesis -/

section SubgraphPromotion
omit [DecidableEq V]

/-- Regard a subgraph of `G` as a subgraph of a larger graph.  Its vertex set and
adjacency relation are unchanged (not merely isomorphic). -/
def promoteSubgraph (hGH : G ≤ H) (K : G.Subgraph) : H.Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub := fun h => hGH (K.adj_sub h)
  edge_vert := K.edge_vert
  symm := K.symm

@[simp] theorem promoteSubgraph_verts (hGH : G ≤ H) (K : G.Subgraph) :
    (promoteSubgraph hGH K).verts = K.verts := rfl

@[simp] theorem promoteSubgraph_adj (hGH : G ≤ H) (K : G.Subgraph) (u v : V) :
    (promoteSubgraph hGH K).Adj u v ↔ K.Adj u v := Iff.rfl

@[simp] theorem promoteSubgraph_spanningCoe (hGH : G ≤ H) (K : G.Subgraph) :
    (promoteSubgraph hGH K).spanningCoe = K.spanningCoe := rfl

variable [Fintype V] {B : ℕ → ℕ}

theorem SmallCuts.mono (hG : SmallCuts G B) (hHG : H ≤ G) : SmallCuts H B := by
  intro k hk K hK
  simpa only [promoteSubgraph_spanningCoe] using
    hG k hk (promoteSubgraph hHG K) hK

end SubgraphPromotion

section SmallCutsConsequences
variable [Fintype V] {B : ℕ → ℕ}

theorem SmallCuts.mask (hG : SmallCuts G B) (Z : Set V) : SmallCuts (mask G Z) B :=
  hG.mono (mask_le G Z)

omit [DecidableEq V]

theorem SmallCuts.deleteEdges (hG : SmallCuts G B) (S : Set (Sym2 V)) :
    SmallCuts (G.deleteEdges S) B :=
  hG.mono (G.deleteEdges_le S)

theorem SmallCuts.spanningCoe (hG : SmallCuts G B) (K : G.Subgraph) :
    SmallCuts K.spanningCoe B :=
  hG.mono K.spanningCoe_le

end SmallCutsConsequences

/-! ## Boolean and three-color helpers -/

section Coloring
omit [DecidableEq V]
variable {Z : Set V} {p : V → Bool}

theorem properOff_iff_proper_mask :
    ProperOff G Z p ↔ ∀ ⦃u v⦄, (mask G Z).Adj u v → p u ≠ p v := by
  constructor
  · intro hp u v h
    exact hp h.1 h.2.1 h.2.2
  · intro hp u v huv hu hv
    exact hp ⟨huv, hu, hv⟩

theorem colorable_two_of_proper (hp : ∀ ⦃u v⦄, G.Adj u v → p u ≠ p v) :
    G.Colorable 2 := by
  simpa using (Coloring.mk p (fun {_ _} h => hp h)).colorable

theorem colorable_two_iff_exists_bool :
    G.Colorable 2 ↔ ∃ p : V → Bool, ∀ ⦃u v⦄, G.Adj u v → p u ≠ p v := by
  constructor
  · intro hc
    let c : G.Coloring Bool := hc.toColoring (by decide)
    exact ⟨c, fun {_ _} h => c.valid h⟩
  · rintro ⟨p, hp⟩
    exact colorable_two_of_proper hp

theorem colorable_mask_of_properOff (hp : ProperOff G Z p) : (mask G Z).Colorable 2 :=
  colorable_two_of_proper (properOff_iff_proper_mask.mp hp)

theorem colorable_mask_iff_exists_properOff :
    (mask G Z).Colorable 2 ↔ ∃ p : V → Bool, ProperOff G Z p := by
  simp only [colorable_two_iff_exists_bool, properOff_iff_proper_mask]

/-- Give `Z` the third color (`none`) and use the Boolean map off `Z`. -/
theorem colorable_three_of_independent_properOff (hZ : Independent G Z)
    (hp : ProperOff G Z p) : G.Colorable 3 := by
  classical
  let c : V → Option Bool := fun v => if v ∈ Z then none else some (p v)
  have hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v := by
    intro u v huv
    by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z
    · exact (hZ huv hu hv).elim
    · simp [c, hu, hv]
    · simp [c, hu, hv]
    · simpa [c, hu, hv] using hp huv hu hv
  simpa using (Coloring.mk c (fun {_ _} h => hc h)).colorable

theorem colorable_three_of_independent_colorable_mask (hZ : Independent G Z)
    (hc : (mask G Z).Colorable 2) : G.Colorable 3 := by
  rcases colorable_mask_iff_exists_properOff.mp hc with ⟨p, hp⟩
  exact colorable_three_of_independent_properOff hZ hp

end Coloring

end E74
