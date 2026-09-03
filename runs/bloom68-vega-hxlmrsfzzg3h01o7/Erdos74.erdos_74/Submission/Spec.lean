import FormalConjecturesUtil

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?
-/
theorem erdos_74 : ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) := by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74

/-
## Disproof

We construct a slowly divergent budget for which all finite subgraphs are
three-colorable.  The key step constructs an independent odd-cycle transversal
localized near an arbitrary cut's bad edges.  Short closed-walk parity supports
reduce the number of bad edges; separated buffers let every stage reuse the
same third color.  Compactness then supplies a three-coloring of the whole graph.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V]

/-- The edges on which a two-valued assignment fails to be proper. -/
def badGraph (G : SimpleGraph V) (p : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ p u = p v
  symm := fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩
  loopless := fun v h ↦ G.loopless v h.1

noncomputable def badEdges [Fintype V] (G : SimpleGraph V) (p : V → Bool) :
    Finset (Sym2 V) := by
  classical
  exact (badGraph G p).edgeFinset

noncomputable def ends (E : Finset (Sym2 V)) : Finset V := by
  classical
  exact E.biUnion Sym2.toFinset

/-- A vertex deletion, represented on the unchanged ambient type. -/
def mask (G : SimpleGraph V) (Z : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ Z ∧ v ∉ Z
  symm := fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := fun v h ↦ G.loopless v h.1

def Independent (G : SimpleGraph V) (Z : Set V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ Z → v ∈ Z → False

def ProperOff (G : SimpleGraph V) (Z : Set V) (p : V → Bool) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∉ Z → v ∉ Z → p u ≠ p v

/-- Bounded reachability; unlike natural graph distance, this handles disconnected vertices. -/
def Near (G : SimpleGraph V) (X : Set V) (r : ℕ) (v : V) : Prop :=
  ∃ x ∈ X, ∃ w : G.Walk v x, w.length ≤ r

/-- Sum of edge labels, retaining multiplicities along a walk. -/
def walkXor {G : SimpleGraph V} (a : Sym2 V → Bool) {u v : V} : G.Walk u v → Bool
  | .nil => false
  | @Walk.cons _ _ u v w h p => a s(u, v) ^^ walkXor a p

noncomputable def twist (S : Finset (Sym2 V)) (e : Sym2 V) : Bool := by
  classical
  exact !decide (e ∈ S)

/-- A finite support for all parity constraints at a given length scale. -/
def ShortSupport (G : SimpleGraph V) (L : ℕ) (S : Finset (Sym2 V)) : Prop :=
  (S : Set (Sym2 V)) ⊆ G.edgeSet ∧
  ∀ (v : V) (w : G.Walk v v), w.length ≤ L → walkXor (twist S) w = false

def MinimalSupport (G : SimpleGraph V) (L : ℕ) (S : Finset (Sym2 V)) : Prop :=
  ShortSupport G L S ∧ ∀ T, ShortSupport G L T → S.card ≤ T.card

/-- The only hereditary numerical hypothesis used in the finite coloring argument. -/
def SmallCuts [Fintype V] (G : SimpleGraph V) (B : ℕ → ℕ) : Prop :=
  ∀ k, 2 ≤ k → ∀ H : G.Subgraph, H.verts.ncard ≤ B k →
    ∃ p : V → Bool, (badEdges H.spanningCoe p).card < k

omit [DecidableEq V] in
@[simp] theorem badGraph_adj (G : SimpleGraph V) (p : V → Bool) (u v : V) :
    (badGraph G p).Adj u v ↔ G.Adj u v ∧ p u = p v := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem mask_adj (G : SimpleGraph V) (Z : Set V) (u v : V) :
    (mask G Z).Adj u v ↔ G.Adj u v ∧ u ∉ Z ∧ v ∉ Z := Iff.rfl

omit [DecidableEq V] in
theorem mask_le (G : SimpleGraph V) (Z : Set V) : mask G Z ≤ G := fun _ _ h ↦ h.1

@[simp] theorem mem_badEdges [Fintype V] (G : SimpleGraph V) (p : V → Bool) (u v : V) :
    s(u, v) ∈ badEdges G p ↔ G.Adj u v ∧ p u = p v := by
  classical
  simp [badEdges]

@[simp] theorem mem_ends {E : Finset (Sym2 V)} {v : V} :
    v ∈ ends E ↔ ∃ e ∈ E, v ∈ e := by
  classical
  simp [ends]

@[simp] theorem ends_empty : ends (∅ : Finset (Sym2 V)) = ∅ := by
  classical
  simp [ends]

@[simp] theorem ends_union (E F : Finset (Sym2 V)) : ends (E ∪ F) = ends E ∪ ends F := by
  classical
  ext v
  simp only [mem_ends, Finset.mem_union]
  aesop

theorem card_ends_le (E : Finset (Sym2 V)) : (ends E).card ≤ 2 * E.card := by
  classical
  dsimp [ends]
  simpa [Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul E Sym2.toFinset 2 (fun e _ ↦ by rw [Sym2.card_toFinset]; split_ifs <;> omega)

omit [DecidableEq V] in
@[simp] theorem walkXor_nil {G : SimpleGraph V} (a : Sym2 V → Bool) (v : V) :
    walkXor a (Walk.nil : G.Walk v v) = false := rfl

omit [DecidableEq V] in
@[simp] theorem walkXor_cons {G : SimpleGraph V} (a : Sym2 V → Bool)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkXor a (p.cons h) = (a s(u, v) ^^ walkXor a p) := rfl

end E74

/- Recursive bounds and their inverse budget for the Erdős 74 argument. -/

namespace E74

/-- The radius used by the localized induction. -/
def radiusBound : ℕ → ℕ
  | 0 => 0
  | t + 1 => (t + 1) * (16 * (t + 1) * (radiusBound t + 2)) + radiusBound t + 3

/-- The short-cycle length at stage `t`. -/
def lengthBound (t : ℕ) : ℕ := 16 * t * (radiusBound (t - 1) + 2)

/-- The vertex bound for a certificate of order `t`. -/
def certificateBound (t : ℕ) : ℕ := 2 * lengthBound t ^ t

@[simp] theorem radiusBound_zero : radiusBound 0 = 0 := rfl

@[simp] theorem lengthBound_zero : lengthBound 0 = 0 := rfl

@[simp] theorem lengthBound_succ (t : ℕ) :
    lengthBound (t + 1) = 16 * (t + 1) * (radiusBound t + 2) := by
  simp [lengthBound]

@[simp] theorem certificateBound_zero : certificateBound 0 = 2 := rfl

theorem radiusBound_succ (t : ℕ) :
    radiusBound (t + 1) = (t + 1) * lengthBound (t + 1) + radiusBound t + 3 := by
  rw [lengthBound_succ]
  rfl

theorem radiusBound_monotone : Monotone radiusBound := by
  apply monotone_nat_of_le_succ
  intro t
  rw [radiusBound_succ]
  omega

theorem lengthBound_monotone : Monotone lengthBound := by
  intro s t h
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 h)
    (Nat.add_le_add_right (radiusBound_monotone (Nat.sub_le_sub_right h 1)) 2)

theorem radiusBound_eq {t : ℕ} (ht : 0 < t) :
    radiusBound t = t * lengthBound t + radiusBound (t - 1) + 3 := by
  cases t with
  | zero => omega
  | succ t => simpa using radiusBound_succ t

theorem le_lengthBound (t : ℕ) : t ≤ lengthBound t := by
  unfold lengthBound
  nlinarith [Nat.zero_le (t * radiusBound (t - 1))]

theorem two_le_lengthBound {t : ℕ} (ht : 0 < t) : 2 ≤ lengthBound t := by
  unfold lengthBound
  nlinarith [Nat.zero_le (t * radiusBound (t - 1))]

theorem lengthBound_pos {t : ℕ} (ht : 0 < t) : 0 < lengthBound t :=
  lt_of_lt_of_le (by decide : 0 < 2) (two_le_lengthBound ht)

theorem radiusBound_le_pred {s t : ℕ} (h : s < t) :
    radiusBound s ≤ radiusBound (t - 1) :=
  radiusBound_monotone (by omega)

theorem radiusBound_comp_le {s t : ℕ} (ht : 0 < t) (h : s ≤ t) :
    s * lengthBound t + radiusBound (t - 1) + 3 ≤ radiusBound t := by
  rw [radiusBound_eq ht]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right (lengthBound t) h) _) _

theorem radiusBound_comp {s t : ℕ} (h : s < t) :
    s * lengthBound t + radiusBound (t - 1) + 3 ≤ radiusBound t :=
  radiusBound_comp_le (by omega) h.le

theorem two_le_certificateBound (t : ℕ) : 2 ≤ certificateBound t := by
  cases t with
  | zero => simp
  | succ t =>
    exact Nat.mul_le_mul_left 2
      (Nat.one_le_pow (t + 1) (lengthBound (t + 1)) (lengthBound_pos (by omega)))

theorem certificateBound_monotone : Monotone certificateBound := by
  intro s t h
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simpa using two_le_certificateBound t
  · exact Nat.mul_le_mul_left 2
      ((Nat.pow_le_pow_left (lengthBound_monotone h) s).trans
        (Nat.pow_le_pow_right (lengthBound_pos (hs.trans_le h)) h))

theorem le_certificateBound (t : ℕ) : t ≤ certificateBound t := by
  cases t with
  | zero => exact Nat.zero_le _
  | succ t =>
    calc
      t + 1 ≤ lengthBound (t + 1) := le_lengthBound _
      _ ≤ lengthBound (t + 1) ^ (t + 1) := Nat.le_pow (Nat.succ_pos t)
      _ ≤ certificateBound (t + 1) := Nat.le_mul_of_pos_left _ (by decide)

theorem certificateBound_unbounded (n : ℕ) : n ≤ certificateBound (n + 1) :=
  (Nat.le_succ n).trans (le_certificateBound (n + 1))

/-- The least `k` for which `n ≤ certificateBound (k + 1)`. -/
noncomputable def budget (n : ℕ) : ℕ :=
  Nat.find (show ∃ k, n ≤ certificateBound (k + 1) from
    ⟨n, certificateBound_unbounded n⟩)

theorem budget_spec (n : ℕ) : n ≤ certificateBound (budget n + 1) :=
  Nat.find_spec (p := fun k => n ≤ certificateBound (k + 1)) _

theorem budget_le {n k : ℕ} (h : n ≤ certificateBound (k + 1)) : budget n ≤ k :=
  Nat.find_min' _ h

theorem budget_le_iff {n k : ℕ} : budget n ≤ k ↔ n ≤ certificateBound (k + 1) :=
  ⟨fun h => (budget_spec n).trans (certificateBound_monotone (Nat.add_le_add_right h 1)),
    budget_le⟩

theorem budget_monotone : Monotone budget := by
  intro m n h
  exact budget_le (h.trans (budget_spec n))

theorem budget_lt {n t : ℕ} (ht : 0 < t) (h : n ≤ certificateBound t) : budget n < t := by
  have hb : budget n ≤ t - 1 := budget_le (by simpa [Nat.sub_add_cancel ht] using h)
  omega

theorem budget_tendsto_atTop : Filter.Tendsto budget Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun t => ⟨certificateBound t + 1, ?_⟩
  intro n hn
  by_contra h
  have hb : budget n + 1 ≤ t := by omega
  have := (budget_spec n).trans (certificateBound_monotone hb)
  omega

end E74

/-
# Bounded walks, edge supports, and elementary coloring utilities

All neighborhood statements use `E74.Near`, hence require an actual walk even
between vertices in different connected components.  No numerical graph distance
or parity argument is used here.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V]

/- ## Endpoints of finite edge sets -/

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

/- ## Bounded reachability -/

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

/- ## First-hit invariance under edge deletion -/

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

/- ## Bad edges -/

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

/- ## Downward heredity of the small-cut hypothesis -/

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

/- ## Boolean and three-color helpers -/

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

/-
# Walk parity and short supports

Parity is computed on the complete edge list, with multiplicities.  All support
constraints concern closed walks, not just cycles.  In particular, no cycle
decomposition is needed for cut telescoping or for the certificate lemmas.
-/

open SimpleGraph
open scoped symmDiff

namespace E74

universe u
variable {V : Type u} [DecidableEq V]
variable {G H : SimpleGraph V} {u v x y : V}

/- ## Total edge labels -/

section TotalLabels
omit [DecidableEq V]

/-- The recursive sum is a fold over the edge list, retaining multiplicities. -/
theorem walkXor_eq_foldr (a : Sym2 V → Bool) (w : G.Walk u v) :
    walkXor a w = w.edges.foldr (fun e b => a e ^^ b) false := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [ih]

/-- Equal edge lists give equal sums, even in different graphs. -/
theorem walkXor_eq_of_edges_eq (a : Sym2 V → Bool)
    (w : G.Walk u v) (q : H.Walk x y) (h : w.edges = q.edges) :
    walkXor a w = walkXor a q := by
  simp only [walkXor_eq_foldr, h]

/-- Only pointwise agreement on the edges actually traversed is needed. -/
theorem walkXor_congr {a b : Sym2 V → Bool} (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, a e = b e) : walkXor a w = walkXor b w := by
  induction w with
  | nil => rfl
  | @cons u v x huv w ih =>
    simp only [walkXor_cons]
    rw [h s(u, v) (by simp), ih (fun e he => h e (by simp [he]))]

@[simp] theorem walkXor_append (a : Sym2 V → Bool)
    (w : G.Walk u v) (q : G.Walk v x) :
    walkXor a (w.append q) = (walkXor a w ^^ walkXor a q) := by
  induction w with
  | nil => simp
  | cons h w ih => simp [ih]

@[simp] theorem walkXor_reverse (a : Sym2 V → Bool) (w : G.Walk u v) :
    walkXor a w.reverse = walkXor a w := by
  induction w with
  | nil => simp
  | @cons u v x huv w ih =>
    simp [ih, Sym2.eq_swap, Bool.xor_comm]

@[simp] theorem walkXor_copy (a : Sym2 V → Bool) (w : G.Walk u v)
    (hu : u = x) (hv : v = y) : walkXor a (w.copy hu hv) = walkXor a w := by
  subst x y
  rfl

@[simp] theorem walkXor_mapLe (a : Sym2 V → Bool) (hGH : G ≤ H)
    (w : G.Walk u v) : walkXor a (w.mapLe hGH) = walkXor a w :=
  walkXor_eq_of_edges_eq a _ _ (w.edges_mapLe_eq_edges hGH)

@[simp] theorem walkXor_transfer (a : Sym2 V → Bool) (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, e ∈ H.edgeSet) :
    walkXor a (w.transfer H h) = walkXor a w :=
  walkXor_eq_of_edges_eq a _ _ (w.edges_transfer h)

@[simp] theorem walkXor_false (w : G.Walk u v) :
    walkXor (fun _ => false) w = false := by
  induction w <;> simp_all

/-- XOR is linear in the total edge label. -/
theorem walkXor_xor (a b : Sym2 V → Bool) (w : G.Walk u v) :
    walkXor (fun e => a e ^^ b e) w = (walkXor a w ^^ walkXor b w) := by
  induction w with
  | nil => rfl
  | @cons u v x huv w ih =>
    simp only [walkXor_cons, ih]
    cases a s(u, v) <;> cases b s(u, v) <;>
      cases walkXor a w <;> cases walkXor b w <;> rfl

/-- Unequal sums have an edge on which the labels differ. -/
theorem exists_edge_of_walkXor_ne {a b : Sym2 V → Bool} (w : G.Walk u v)
    (h : walkXor a w ≠ walkXor b w) : ∃ e ∈ w.edges, a e ≠ b e := by
  by_contra hn
  apply h
  apply walkXor_congr w
  intro e he
  by_contra hab
  exact hn ⟨e, he, hab⟩

end TotalLabels

/- ## Membership labels and their differences -/

@[simp] theorem twist_of_mem {S : Finset (Sym2 V)} {e : Sym2 V} (h : e ∈ S) :
    twist S e = false := by
  classical
  simp [twist, h]

@[simp] theorem twist_of_not_mem {S : Finset (Sym2 V)} {e : Sym2 V} (h : e ∉ S) :
    twist S e = true := by
  classical
  simp [twist, h]

@[simp] theorem twist_eq_false_iff {S : Finset (Sym2 V)} {e : Sym2 V} :
    twist S e = false ↔ e ∈ S := by
  classical
  simp [twist]

@[simp] theorem twist_eq_true_iff {S : Finset (Sym2 V)} {e : Sym2 V} :
    twist S e = true ↔ e ∉ S := by
  classical
  simp [twist]

/-- This also applies directly to an unordered pair `s(u, v)`. -/
theorem twist_congr {S T : Finset (Sym2 V)} {e : Sym2 V}
    (h : e ∈ S ↔ e ∈ T) : twist S e = twist T e := by
  classical
  simp only [twist, h]

theorem walkXor_twist_congr {S T : Finset (Sym2 V)} (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, e ∈ S ↔ e ∈ T) :
    walkXor (twist S) w = walkXor (twist T) w :=
  walkXor_congr w (fun e he => twist_congr (h e he))

/-- Complementing both membership labels cancels under XOR. -/
theorem twist_xor_twist (S T : Finset (Sym2 V)) (e : Sym2 V) :
    (twist S e ^^ twist T e) = decide (e ∈ S ∆ T) := by
  classical
  by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;>
    simp [twist, Finset.mem_symmDiff, hS, hT]

/-- The difference of two twisted sums is the indicator sum of their symmetric difference. -/
theorem walkXor_twist_xor_twist (S T : Finset (Sym2 V)) (w : G.Walk u v) :
    (walkXor (twist S) w ^^ walkXor (twist T) w) =
      walkXor (fun e => decide (e ∈ S ∆ T)) w := by
  rw [← walkXor_xor]
  exact walkXor_congr w (fun e _ => twist_xor_twist S T e)

/-- If nested supports have different sums, a traversed edge lies in the difference. -/
theorem exists_edge_mem_sdiff_of_walkXor_twist_ne {S T : Finset (Sym2 V)}
    (hST : S ⊆ T) (w : G.Walk u v)
    (h : walkXor (twist S) w ≠ walkXor (twist T) w) :
    ∃ e ∈ w.edges, e ∈ T ∧ e ∉ S := by
  obtain ⟨e, he, hne⟩ := exists_edge_of_walkXor_ne w h
  have hnS : e ∉ S := by
    intro hS
    exact hne (by simp [hS, hST hS])
  have hT : e ∈ T := by
    by_contra hnT
    exact hne (by simp [hnS, hnT])
  exact ⟨e, he, hT, hnS⟩

/- ## Cut telescoping -/

/-- On an actual graph edge, the twisted bad-edge label is the endpoint XOR. -/
theorem twist_badEdges [Fintype V] (p : V → Bool) (huv : G.Adj u v) :
    twist (badEdges G p) s(u, v) = (p u ^^ p v) := by
  classical
  simp only [twist, mem_badEdges, huv, true_and]
  cases p u <;> cases p v <;> rfl

/-- The XOR of an exact endpoint-difference label telescopes along every walk. -/
theorem walkXor_eq_endpoints {a : Sym2 V → Bool} (p : V → Bool)
    (w : G.Walk u v)
    (ha : ∀ x y, G.Adj x y → a s(x, y) = (p x ^^ p y)) :
    walkXor a w = (p u ^^ p v) := by
  induction w with
  | nil => simp
  | @cons u v x huv w ih =>
    rw [walkXor_cons, ha u v huv, ih]
    cases p u <;> cases p v <;> cases p x <;> rfl

theorem walkXor_twist_badEdges [Fintype V] (p : V → Bool) (w : G.Walk u v) :
    walkXor (twist (badEdges G p)) w = (p u ^^ p v) :=
  walkXor_eq_endpoints p w (fun _ _ h => twist_badEdges p h)

@[simp] theorem walkXor_twist_badEdges_closed [Fintype V]
    (p : V → Bool) (w : G.Walk v v) :
    walkXor (twist (badEdges G p)) w = false := by
  simp [walkXor_twist_badEdges]

/-- Every true cut is a short support, at every length scale. -/
theorem shortSupport_badEdges [Fintype V] (G : SimpleGraph V) (L : ℕ) (p : V → Bool) :
    ShortSupport G L (badEdges G p) := by
  constructor
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v => exact ((mem_badEdges G p u v).mp he).1
  · intro v w _
    exact walkXor_twist_badEdges_closed p w

/- ## Transporting and pruning short supports -/

variable {L M : ℕ} {S T D A : Finset (Sym2 V)}

theorem ShortSupport.mono_length (hS : ShortSupport G L S) (hML : M ≤ L) :
    ShortSupport G M S :=
  ⟨hS.1, fun v w hw => hS.2 v w (hw.trans hML)⟩

/-- Restrict to a smaller graph when all edges of the support survive. -/
theorem ShortSupport.of_le (hS : ShortSupport G L S) (hHG : H ≤ G)
    (hSH : (S : Set (Sym2 V)) ⊆ H.edgeSet) : ShortSupport H L S := by
  refine ⟨hSH, ?_⟩
  intro v w hw
  simpa using hS.2 v (w.mapLe hHG) (by simpa using hw)

theorem ShortSupport.mask (hS : ShortSupport G L S) (Z : Set V)
    (hSZ : (S : Set (Sym2 V)) ⊆ (mask G Z).edgeSet) :
    ShortSupport (mask G Z) L S :=
  hS.of_le (mask_le G Z) hSZ

/-- In particular, deleting vertices away from the support endpoints preserves it. -/
theorem ShortSupport.mask_of_disjoint_ends (hS : ShortSupport G L S) {Z : Set V}
    (hSZ : Disjoint (ends S : Set V) Z) : ShortSupport (E74.mask G Z) L S := by
  apply hS.mask Z
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    change G.Adj u v ∧ u ∉ Z ∧ v ∉ Z
    refine ⟨hS.1 he, ?_, ?_⟩
    · exact fun hu => Set.disjoint_left.mp hSZ
        (mem_ends.mpr ⟨s(u, v), he, Sym2.mem_mk_left u v⟩) hu
    · exact fun hv => Set.disjoint_left.mp hSZ
        (mem_ends.mpr ⟨s(u, v), he, Sym2.mem_mk_right u v⟩) hv

/-- A replacement support is valid when all short closed-walk sums are unchanged. -/
theorem ShortSupport.congr (hS : ShortSupport G L S)
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet)
    (hxor : ∀ v (w : G.Walk v v), w.length ≤ L →
      walkXor (twist T) w = walkXor (twist S) w) : ShortSupport G L T :=
  ⟨hT, fun v w hw => (hxor v w hw).trans (hS.2 v w hw)⟩

/-- Pointwise agreement is required only on the edges of short closed walks. -/
theorem ShortSupport.congr_edges (hS : ShortSupport G L S)
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet)
    (hmem : ∀ v (w : G.Walk v v), w.length ≤ L →
      ∀ e ∈ w.edges, e ∈ T ↔ e ∈ S) : ShortSupport G L T :=
  hS.congr hT (fun v w hw => walkXor_twist_congr w (hmem v w hw))

/-- Pruning any set is allowed if it leaves every short closed-walk sum unchanged. -/
theorem ShortSupport.sdiff (hS : ShortSupport G L S) (A : Finset (Sym2 V))
    (hxor : ∀ v (w : G.Walk v v), w.length ≤ L →
      walkXor (twist (S \ A)) w = walkXor (twist S) w) :
    ShortSupport G L (S \ A) :=
  hS.congr (fun _ he => hS.1 (Finset.sdiff_subset he)) hxor

/-- A parity formulation of replacement: the symmetric-difference indicator sums to zero. -/
theorem ShortSupport.of_symmDiff (hS : ShortSupport G L S)
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet)
    (hzero : ∀ v (w : G.Walk v v), w.length ≤ L →
      walkXor (fun e => decide (e ∈ T ∆ S)) w = false) : ShortSupport G L T := by
  apply hS.congr hT
  intro v w hw
  have h := (walkXor_twist_xor_twist T S w).trans (hzero v w hw)
  cases hT' : walkXor (twist T) w <;> cases hS' : walkXor (twist S) w <;>
    simp_all

/- ## Minimal cardinality -/

theorem exists_shortSupport [Finite V] (G : SimpleGraph V) (L : ℕ) :
    ∃ S, ShortSupport G L S := by
  letI := Fintype.ofFinite V
  exact ⟨badEdges G (fun _ => false), shortSupport_badEdges G L (fun _ => false)⟩

/-- A minimum-cardinality support exists, by minimizing its natural-number cardinality. -/
theorem exists_minimalSupport [Finite V] (G : SimpleGraph V) (L : ℕ) :
    ∃ S, MinimalSupport G L S := by
  classical
  have hex : ∃ n : ℕ, ∃ S : Finset (Sym2 V), ShortSupport G L S ∧ S.card = n := by
    obtain ⟨S, hS⟩ := exists_shortSupport G L
    exact ⟨S.card, S, hS, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  rw [hcard]
  exact Nat.find_min' hex ⟨T, hT, rfl⟩

theorem MinimalSupport.card_le (hS : MinimalSupport G L S) (hT : ShortSupport G L T) :
    S.card ≤ T.card := hS.2 T hT

/-- A minimum short support is no larger than the bad-edge support of any cut. -/
theorem MinimalSupport.card_le_badEdges [Fintype V] (hS : MinimalSupport G L S)
    (p : V → Bool) : S.card ≤ (badEdges G p).card :=
  hS.card_le (shortSupport_badEdges G L p)

/- ## Certificate-facing witnesses -/

/-- Any violated short constraint for a subset exposes a missing support edge. -/
theorem ShortSupport.exists_edge_not_mem (hS : ShortSupport G L S) (hD : D ⊆ S)
    (w : G.Walk v v) (hw : w.length ≤ L) (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ S ∧ e ∉ D := by
  apply exists_edge_mem_sdiff_of_walkXor_twist_ne hD w
  simpa only [hS.2 v w hw] using hxor

/-- For a true cut the witness theorem needs no length bound at all. -/
theorem exists_badEdge_not_mem_of_walkXor_ne_false [Fintype V]
    (p : V → Bool) (hD : D ⊆ badEdges G p) (w : G.Walk v v)
    (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ badEdges G p ∧ e ∉ D := by
  apply exists_edge_mem_sdiff_of_walkXor_twist_ne hD w
  simpa only [walkXor_twist_badEdges_closed] using hxor

/-- The bounded form used by short-walk certificates. -/
theorem exists_badEdge_not_mem_of_short_walkXor_ne_false [Fintype V]
    (p : V → Bool) (hD : D ⊆ badEdges G p) (w : G.Walk v v)
    (hw : w.length ≤ L) (hxor : walkXor (twist D) w ≠ false) :
    ∃ e ∈ w.edges, e ∈ badEdges G p ∧ e ∉ D :=
  (shortSupport_badEdges G L p).exists_edge_not_mem hD w hw hxor

end E74

/-
# Finite certificates for short parity supports

If every short support has at least `t` edges, a finite branching search produces
an actual subgraph on at most `2 * L ^ t` vertices on which every Boolean cut has
at least `t` bad edges.  A node records a set `D` of distinct edges already chosen.
It chooses a violated closed walk and branches over the walk's edges outside `D`.

The recursive invariant is stated for every graph containing the certificate.
Consequently, the edges in `D` need not be added to a leaf certificate: a leaf is
the empty subgraph, and its conclusion follows from the assumed badness of `D`.
Only vertices of the chosen nonempty closed walks are counted.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u}

section Search
variable [DecidableEq V]

/-- The vertex budget for a search of the given remaining depth. -/
private def searchVertexBound (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => L + L * searchVertexBound L n

private theorem searchVertexBound_add_two_le {L : ℕ} (hL : 2 ≤ L) (n : ℕ) :
    searchVertexBound L n + 2 ≤ 2 * L ^ n := by
  induction n with
  | zero => simp [searchVertexBound]
  | succ n ih =>
    calc
      searchVertexBound L (n + 1) + 2 = L + L * searchVertexBound L n + 2 := rfl
      _ ≤ L * (searchVertexBound L n + 2) := by nlinarith
      _ ≤ L * (2 * L ^ n) := Nat.mul_le_mul_left L ih
      _ = 2 * L ^ (n + 1) := by rw [pow_succ]; ring

/-- In a nonempty closed walk the initial vertex occurs again at the end, so
there are at most `length` distinct vertices, not merely `length + 1`. -/
private theorem closedWalk_verts_ncard_le_length {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hne : w ≠ Walk.nil) : w.toSubgraph.verts.ncard ≤ w.length := by
  classical
  have hcard : w.support.toFinset.card ≤ w.length := by
    cases w with
    | nil => exact (hne rfl).elim
    | cons h q =>
      simp only [Walk.support_cons, List.toFinset_cons, Walk.length_cons]
      rw [Finset.insert_eq_of_mem (List.mem_toFinset.mpr q.end_mem_support)]
      simpa only [Walk.length_support] using q.support.toFinset_card_le
  simpa only [Walk.verts_toSubgraph, ← List.coe_toFinset, Set.ncard_coe_finset] using hcard

/-- A failed support exposes a short closed walk with nonzero twisted sum. -/
private theorem exists_violated_closedWalk {G : SimpleGraph V} {L t : ℕ}
    (hno : ¬ ∃ S, ShortSupport G L S ∧ S.card < t)
    (D : Finset (Sym2 V)) (hD : (D : Set (Sym2 V)) ⊆ G.edgeSet) (hcard : D.card < t) :
    ∃ (v : V) (w : G.Walk v v), w.length ≤ L ∧ walkXor (twist D) w ≠ false := by
  classical
  by_contra hn
  apply hno
  refine ⟨D, ⟨hD, ?_⟩, hcard⟩
  intro v w hw
  by_contra hxor
  exact hn ⟨v, w, hw, hxor⟩

/-- The finite search invariant.  For every containing graph and every cut,
if the previously selected edges are bad, at least `t` edges are bad. -/
private theorem exists_search_certificate [Fintype V] (G : SimpleGraph V) (L t : ℕ)
    (hno : ¬ ∃ S, ShortSupport G L S ∧ S.card < t) (n : ℕ)
    (D : Finset (Sym2 V)) (hD : (D : Set (Sym2 V)) ⊆ G.edgeSet)
    (hdepth : D.card + n = t) :
    ∃ H : G.Subgraph, H.verts.ncard ≤ searchVertexBound L n ∧
      ∀ (K : SimpleGraph V), H.spanningCoe ≤ K → ∀ p : V → Bool,
        D ⊆ badEdges K p → t ≤ (badEdges K p).card := by
  classical
  induction n generalizing D with
  | zero =>
    refine ⟨⊥, by simp [searchVertexBound], ?_⟩
    intro K _ p hbad
    simpa only [Nat.add_zero] using hdepth.symm.trans_le (Finset.card_le_card hbad)
  | succ n ih =>
    obtain ⟨v, w, hw, hxor⟩ := exists_violated_closedWalk hno D hD (by omega)
    have hne : w ≠ Walk.nil := by
      intro heq
      subst w
      exact hxor rfl
    let A : Finset (Sym2 V) := w.edges.toFinset \ D
    have hA (e : A) : (e : Sym2 V) ∈ w.edges ∧ (e : Sym2 V) ∉ D := by
      simpa only [A, Finset.mem_sdiff, List.mem_toFinset] using e.property
    have hAc : A.card ≤ L := by
      calc
        A.card ≤ w.edges.toFinset.card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ w.edges.length := w.edges.toFinset_card_le
        _ = w.length := w.length_edges
        _ ≤ L := hw
    have hchild (e : A) :
        ∃ H : G.Subgraph, H.verts.ncard ≤ searchVertexBound L n ∧
          ∀ (K : SimpleGraph V), H.spanningCoe ≤ K → ∀ p : V → Bool,
            insert (e : Sym2 V) D ⊆ badEdges K p → t ≤ (badEdges K p).card := by
      apply ih (insert (e : Sym2 V) D)
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact w.edges_subset_edgeSet (hA e).1
        · exact hD hf
      · rw [Finset.card_insert_of_notMem (hA e).2]
        omega
    choose C hC using hchild
    let H : G.Subgraph := w.toSubgraph ⊔ ⨆ e : A, C e
    have hwH : w.toSubgraph ≤ H := le_sup_left
    have hCH (e : A) : C e ≤ H := (le_iSup C e).trans le_sup_right
    refine ⟨H, ?_, ?_⟩
    · have hsum : (∑ e : A, (C e).verts.ncard) ≤ A.card * searchVertexBound L n := by
        calc
          (∑ e : A, (C e).verts.ncard) ≤ ∑ _e : A, searchVertexBound L n :=
            Finset.sum_le_sum (fun e _ => (hC e).1)
          _ = A.card * searchVertexBound L n := by simp
      calc
        H.verts.ncard = (w.toSubgraph.verts ∪ ⋃ e : A, (C e).verts).ncard := by
          simp only [H, Subgraph.verts_sup, Subgraph.verts_iSup]
        _ ≤ w.toSubgraph.verts.ncard + (⋃ e : A, (C e).verts).ncard :=
          Set.ncard_union_le _ _
        _ ≤ L + ∑ e : A, (C e).verts.ncard :=
          Nat.add_le_add ((closedWalk_verts_ncard_le_length w hne).trans hw)
            (Set.ncard_iUnion_le_of_fintype _)
        _ ≤ L + A.card * searchVertexBound L n := Nat.add_le_add_left hsum L
        _ ≤ L + L * searchVertexBound L n :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hAc) L
        _ = searchVertexBound L (n + 1) := rfl
    · intro K hHK p hbad
      have hwK : w.toSubgraph.spanningCoe ≤ K :=
        (Subgraph.spanningCoe_le_of_le hwH).trans hHK
      have hedges : ∀ e ∈ w.edges, e ∈ K.edgeSet := by
        intro e he
        apply SimpleGraph.edgeSet_mono hwK
        exact w.mem_edges_toSubgraph.mpr he
      let q : K.Walk v v := w.transfer K hedges
      have hqxor : walkXor (twist D) q ≠ false := by
        simpa only [q, walkXor_transfer] using hxor
      obtain ⟨e, heq, hebad, heD⟩ :=
        exists_badEdge_not_mem_of_walkXor_ne_false p hbad q hqxor
      have hew : e ∈ w.edges := by simpa only [q, Walk.edges_transfer] using heq
      have heA : e ∈ A := Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hew, heD⟩
      exact (hC ⟨e, heA⟩).2 K
        ((Subgraph.spanningCoe_le_of_le (hCH ⟨e, heA⟩)).trans hHK) p
        (Finset.insert_subset_iff.mpr ⟨hebad, hbad⟩)

/-- Absence of a support with fewer than `t` edges has a small, genuine subgraph
certificate: every Boolean cut of that subgraph has at least `t` bad edges. -/
theorem exists_small_cut_certificate [Fintype V] (G : SimpleGraph V) {L t : ℕ}
    (hL : 2 ≤ L) (hno : ¬ ∃ S, ShortSupport G L S ∧ S.card < t) :
    ∃ H : G.Subgraph, H.verts.ncard ≤ 2 * L ^ t ∧
      ∀ p : V → Bool, t ≤ (badEdges H.spanningCoe p).card := by
  obtain ⟨H, hsize, hcert⟩ := exists_search_certificate G L t hno t ∅
    (by simp) (by simp)
  refine ⟨H, hsize.trans ?_, ?_⟩
  · have h := searchVertexBound_add_two_le hL t
    omega
  · intro p
    exact hcert H.spanningCoe le_rfl p (Finset.empty_subset _)

end Search

/-- Hereditarily small cuts force a short parity support of size below `t`. -/
theorem exists_shortSupport_of_smallCuts [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : ℕ → ℕ)
    (hG : SmallCuts G B) {t L : ℕ} (ht : 2 ≤ t) (hL : 2 ≤ L)
    (hB : 2 * L ^ t ≤ B t) : ∃ S, ShortSupport G L S ∧ S.card < t := by
  classical
  by_contra hno
  obtain ⟨H, hsize, hcert⟩ := exists_small_cut_certificate G hL hno
  obtain ⟨p, hp⟩ := hG t ht H (hsize.trans hB)
  exact (not_lt_of_ge (hcert p)) hp

end E74

/-
# Locality of minimum short supports

A minimum short support lies within `S.card * L` of the endpoints of any other
short support, in particular of the bad edges of any Boolean assignment.

We use a finite flood argument instead of shortest paths in the auxiliary graph
of co-occurring edges.  A proper subset `D` of a minimum support violates some
short closed-walk constraint.  Comparing its sum with the sums for `S` and `F`
finds both a new edge of `S \ D` and an edge of `D ∪ F` on the same walk.  Every
endpoint of the new edge is therefore within `L` of the previous flood or `F`.
Adding one edge at a time finishes after exactly `S.card` steps.

All constraints and comparisons use complete walk edge lists, with
multiplicities.  No cycle decomposition is used.  The route between two
vertices on a walk has length at most that walk's length, not twice its length;
this is what gives the exact radius.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Any two vertices occurring on a walk can be joined by a walk no longer than
that walk.  The connecting segment may be traversed in reverse. -/
theorem exists_walk_length_le_of_mem_support {a b x y : V} (w : G.Walk a b)
    (hx : x ∈ w.support) (hy : y ∈ w.support) :
    ∃ q : G.Walk x y, q.length ≤ w.length := by
  revert hx hy
  induction w with
  | @nil a =>
      intro hx hy
      have hxa : x = a := by simpa using hx
      have hya : y = a := by simpa using hy
      subst x y
      exact ⟨Walk.nil, le_rfl⟩
  | @cons a b c hab w ih =>
      intro hx hy
      by_cases hxa : x = a
      · subst x
        exact ⟨(w.cons hab).takeUntil y hy, (w.cons hab).length_takeUntil_le hy⟩
      by_cases hya : y = a
      · subst y
        refine ⟨((w.cons hab).takeUntil x hx).reverse, ?_⟩
        simpa only [Walk.length_reverse] using (w.cons hab).length_takeUntil_le hx
      have hxt : x ∈ w.support := by
        simpa only [Walk.support_cons, List.mem_cons, hxa, false_or] using hx
      have hyt : y ∈ w.support := by
        simpa only [Walk.support_cons, List.mem_cons, hya, false_or] using hy
      obtain ⟨q, hq⟩ := ih hxt hyt
      exact ⟨q, hq.trans (Nat.le_succ w.length)⟩

variable {L r : ℕ} {S F D : Finset (Sym2 V)}

/-- One finite-flood step.  If fewer than `S.card` edges have been reached, a
violated constraint supplies a new edge, all of whose endpoints cost at most
one further `L` in radius.  Only the short-support property of `F` is needed. -/
theorem MinimalSupport.exists_near_edge_of_card_lt
    (hS : MinimalSupport G L S) (hF : ShortSupport G L F)
    (hDS : D ⊆ S) (hcard : D.card < S.card)
    (hD : ∀ v ∈ ends D, Near G (ends F : Set V) r v) :
    ∃ e ∈ S, e ∉ D ∧ ∀ v ∈ e, Near G (ends F : Set V) (r + L) v := by
  classical
  have hbad : ∃ (v : V) (w : G.Walk v v),
      w.length ≤ L ∧ walkXor (twist D) w ≠ false := by
    by_contra! h
    have hvalid : ShortSupport G L D :=
      ⟨fun _ he => hS.1.1 (hDS he), h⟩
    exact (Nat.not_le_of_lt hcard) (hS.card_le hvalid)
  obtain ⟨v, w, hw, hxor⟩ := hbad
  obtain ⟨e, he, heS, heD⟩ := hS.1.exists_edge_not_mem hDS w hw hxor
  have hDF : walkXor (twist D) w ≠ walkXor (twist F) w := by
    rw [hF.2 v w hw]
    exact hxor
  obtain ⟨f, hf, hfne⟩ := exists_edge_of_walkXor_ne w hDF
  have hfmem : f ∈ D ∨ f ∈ F := by
    by_contra! h
    exact hfne (by simp [h.1, h.2])
  have hfnear : Near G (ends F : Set V) r f.out.1 := by
    rcases hfmem with hfD | hfF
    · exact hD f.out.1 (mem_ends_of_mem hfD f.out_fst_mem)
    · exact near_of_mem (mem_ends_of_mem hfF f.out_fst_mem)
  refine ⟨e, heS, heD, ?_⟩
  intro x hx
  obtain ⟨q, hq⟩ := exists_walk_length_le_of_mem_support w
    (Walk.mem_support_of_mem_edges he hx)
    (Walk.mem_support_of_mem_edges hf f.out_fst_mem)
  apply near_mono_radius _ (near_prepend_walk q hfnear)
  have hqL : q.length ≤ L := hq.trans hw
  omega

/-- A minimum short support is local to any short support at the same scale.
Finiteness of the ambient vertex type is not needed for this stronger form. -/
theorem minimalSupport_near_shortSupport
    (hS : MinimalSupport G L S) (hF : ShortSupport G L F) :
    ∀ v ∈ ends S, Near G (ends F : Set V) (S.card * L) v := by
  classical
  have flood : ∀ n, n ≤ S.card →
      ∃ D : Finset (Sym2 V), D ⊆ S ∧ D.card = n ∧
        ∀ v ∈ ends D, Near G (ends F : Set V) (n * L) v := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
        simp
    | succ n ih =>
        intro hn
        obtain ⟨D, hDS, hcard, hD⟩ := ih (Nat.le_of_succ_le hn)
        have hlt : D.card < S.card := by omega
        obtain ⟨e, heS, heD, henear⟩ :=
          hS.exists_near_edge_of_card_lt hF hDS hlt hD
        refine ⟨insert e D, Finset.insert_subset heS hDS, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem heD, hcard]
        · intro v hv
          obtain ⟨f, hf, hvf⟩ := mem_ends.mp hv
          rcases Finset.mem_insert.mp hf with rfl | hf
          · simpa only [Nat.succ_mul] using henear v hvf
          · exact near_mono_radius (Nat.mul_le_mul_right L (Nat.le_succ n))
              (hD v (mem_ends_of_mem hf hvf))
  obtain ⟨D, hDS, hcard, hD⟩ := flood S.card le_rfl
  have hEq : D = S := Finset.eq_of_subset_of_card_le hDS hcard.ge
  simpa only [hEq] using hD

/-- Every endpoint of a minimum short support is within `S.card * L` of a bad
edge of any prescribed Boolean assignment.  `Near` includes an actual walk, so
this also handles disconnected graphs; when `S = ∅` the conclusion is vacuous. -/
theorem minimalSupport_near_badEdges [Fintype V]
    (hS : MinimalSupport G L S) (p : V → Bool) :
    ∀ v ∈ ends S, Near G (ends (badEdges G p) : Set V) (S.card * L) v :=
  minimalSupport_near_shortSupport hS (shortSupport_badEdges G L p)

end E74

/-
# Potentials on a finite set of terminals

A short-walk constraint is represented by an edge in a Boolean double cover of
its terminal set.  If a terminal and its opposite lift were connected, a simple
path in the cover would expand to a short closed walk with nonzero XOR.  Ordering
the two distinct components over each terminal therefore gives a potential.

The cover has twice as many vertices as the terminal set.  This accounts for
the constant `16` in `exists_terminal_assignment`.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V}

/-- The Boolean double cover of all bounded-length terminal constraints.  The
inequality removes graph loops; trivial constraints are handled by reflexive
reachability instead. -/
private def terminalCover (G : SimpleGraph V) (a : Sym2 V → Bool)
    (W : Finset V) (D : ℕ) : SimpleGraph (W × Bool) where
  Adj x y := x ≠ y ∧ ∃ w : G.Walk x.1.1 y.1.1,
    w.length ≤ D ∧ walkXor a w = (x.2 ^^ y.2)
  symm := by
    intro x y h
    obtain ⟨hne, w, hw, hx⟩ := h
    exact ⟨hne.symm, w.reverse, by simpa using hw,
      by simpa [Bool.xor_comm] using hx⟩
  loopless := by
    intro x h
    exact h.1 rfl

omit [DecidableEq V] in
/-- Expand a cover walk, retaining both the length bound and its endpoint XOR. -/
private theorem terminalCover_expand {a : Sym2 V → Bool} {W : Finset V} {D : ℕ}
    {x y : W × Bool} (p : (terminalCover G a W D).Walk x y) :
    ∃ w : G.Walk x.1.1 y.1.1,
      w.length ≤ p.length * D ∧ walkXor a w = (x.2 ^^ y.2) := by
  induction p with
  | nil => exact ⟨Walk.nil, by simp, by simp⟩
  | @cons x y z h p ih =>
    obtain ⟨e, he, hx⟩ := h.2
    obtain ⟨w, hw, hy⟩ := ih
    refine ⟨e.append w, ?_, ?_⟩
    · calc
        (e.append w).length = e.length + w.length := by simp
        _ ≤ D + p.length * D := Nat.add_le_add he hw
        _ = (p.cons h).length * D := by simp [Nat.add_mul, Nat.add_comm]
    · rw [walkXor_append, hx, hy]
      cases x.2 <;> cases y.2 <;> cases z.2 <;> rfl

/-- A single constraint connects the corresponding lifts, even when they agree. -/
private theorem terminalCover_reachable {a : Sym2 V → Bool} {W : Finset V} {D : ℕ}
    {x y : W × Bool} (w : G.Walk x.1.1 y.1.1) (hw : w.length ≤ D)
    (hx : walkXor a w = (x.2 ^^ y.2)) : (terminalCover G a W D).Reachable x y := by
  by_cases h : x = y
  · subst y
    exact Reachable.rfl
  · exact (show (terminalCover G a W D).Adj x y from ⟨h, w, hw, hx⟩).reachable

/-- If all closed walks of length at most `2 * W.card * D` have zero XOR,
then one potential simultaneously respects every walk of length at most `D`
between terminals in `W`.  No finiteness of the ambient vertex type is needed. -/
theorem exists_potential_on_short_walks (a : Sym2 V → Bool) (W : Finset V) (D : ℕ)
    (hzero : ∀ (v : V) (w : G.Walk v v),
      w.length ≤ 2 * W.card * D → walkXor a w = false) :
    ∃ q : V → Bool, ∀ u ∈ W, ∀ v ∈ W, ∀ w : G.Walk u v,
      w.length ≤ D → walkXor a w = (q u ^^ q v) := by
  classical
  let H := terminalCover G a W D
  let c (v : W) (b : Bool) : H.ConnectedComponent := H.connectedComponentMk (v, b)
  have hsep (v : W) : c v false ≠ c v true := by
    intro hc
    obtain ⟨p, hp⟩ := (ConnectedComponent.exact hc).exists_isPath
    obtain ⟨w, hw, hx⟩ := terminalCover_expand p
    have hlen : p.length ≤ 2 * W.card := by
      simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.mul_comm]
        using hp.length_lt.le
    have hz := hzero v.1 w (hw.trans (Nat.mul_le_mul_right D hlen))
    simp [hz] at hx
  letI : LinearOrder H.ConnectedComponent := IsWellOrder.linearOrder WellOrderingRel
  let qW (v : W) : Bool := decide (c v false < c v true)
  have hpot (u v : W) (w : G.Walk u.1 v.1) (hw : w.length ≤ D) :
      walkXor a w = (qW u ^^ qW v) := by
    cases hx : walkXor a w with
    | false =>
      have h0 : c u false = c v false := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      have h1 : c u true = c v true := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      simp [qW, h0, h1]
    | true =>
      have h0 : c u false = c v true := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      have h1 : c u true = c v false := ConnectedComponent.sound
        (terminalCover_reachable w hw (by simp [hx]))
      rcases lt_or_gt_of_ne (hsep v) with hlt | hgt
      · simp [qW, h0, h1, hlt, not_lt_of_gt hlt]
      · simp [qW, h0, h1, hgt, not_lt_of_gt hgt]
  refine ⟨fun v => if hv : v ∈ W then qW ⟨v, hv⟩ else false, ?_⟩
  intro u hu v hv w hw
  simpa only [dif_pos hu, dif_pos hv] using hpot ⟨u, hu⟩ ⟨v, hv⟩ w hw

/-- The terminal assignment needed by buffered parity surgery.  It realizes
exactly the prescribed special edges, and its flip from the old assignment is
constant on terminal pairs joined by a short walk avoiding all special edges. -/
theorem exists_terminal_assignment [Fintype V] {L r : ℕ} {S : Finset (Sym2 V)}
    (p : V → Bool) (hS : ShortSupport G L S) (hs : S.card ≤ (badEdges G p).card)
    (hL : 16 * (badEdges G p).card * (r + 2) ≤ L) :
    ∃ q : V → Bool,
      (∀ u v, G.Adj u v → s(u, v) ∈ badEdges G p ∪ S →
        (q u = q v ↔ s(u, v) ∈ S)) ∧
      (∀ u ∈ ends (badEdges G p ∪ S), ∀ v ∈ ends (badEdges G p ∪ S),
        Near (G.deleteEdges ((badEdges G p ∪ S) : Set (Sym2 V))) {v} (2 * r + 4) u →
          (q u ^^ p u) = (q v ^^ p v)) := by
  classical
  let W := ends (badEdges G p ∪ S)
  let D := 2 * r + 4
  have hW : W.card ≤ 4 * (badEdges G p).card := by
    calc
      W.card ≤ 2 * (badEdges G p ∪ S).card := card_ends_le _
      _ ≤ 2 * ((badEdges G p).card + S.card) :=
        Nat.mul_le_mul_left 2 (Finset.card_union_le _ _)
      _ ≤ 4 * (badEdges G p).card := by omega
  have hbound : 2 * W.card * D ≤ L := by
    calc
      2 * W.card * D ≤ 2 * (4 * (badEdges G p).card) * D :=
        Nat.mul_le_mul_right D (Nat.mul_le_mul_left 2 hW)
      _ = 16 * (badEdges G p).card * (r + 2) := by dsimp [D]; ring
      _ ≤ L := hL
  obtain ⟨q, hq⟩ := exists_potential_on_short_walks (G := G) (twist S) W D
    (fun v w hw => hS.2 v w (hw.trans hbound))
  refine ⟨q, ?_, ?_⟩
  · intro u v huv he
    have huW : u ∈ W := mem_ends_left he
    have hvW : v ∈ W := mem_ends_right he
    have hx := hq u huW v hvW (Walk.cons huv Walk.nil) (by simp [D])
    have hx' : twist S s(u, v) = (q u ^^ q v) := by simpa using hx
    rw [← twist_eq_false_iff, hx']
    cases q u <;> cases q v <;> decide
  · intro u hu v hv hn
    obtain ⟨w, hw⟩ := near_singleton_iff.mp hn
    have hx : walkXor (twist S) w = (p u ^^ p v) := by
      apply walkXor_eq_endpoints p w
      intro x y hxy
      obtain ⟨hxy, he⟩ := SimpleGraph.deleteEdges_adj.mp hxy
      have hnF : s(x, y) ∉ badEdges G p := by
        intro hf
        exact he (Or.inl hf)
      have hnS : s(x, y) ∉ S := by
        intro hs
        exact he (Or.inr hs)
      calc
        twist S s(x, y) = true := twist_of_not_mem hnS
        _ = twist (badEdges G p) s(x, y) := (twist_of_not_mem hnF).symm
        _ = (p x ^^ p y) := twist_badEdges p hxy
    have hq' := hq u hu v hv (w.mapLe (G.deleteEdges_le _)) (by simpa [D] using hw)
    rw [walkXor_mapLe, hx] at hq'
    cases hpu : p u <;> cases hpv : p v <;> cases hqu : q u <;> cases hqv : q v <;>
      simp_all

end E74

/-
# Buffered recoloring from a terminal assignment

This ball-based interpolation assumes only the two constraints on a terminal
assignment, not any short-support or minimality hypothesis.  All neighborhoods
are bounded-walk neighborhoods, so empty terminal phases and disconnected
vertices require no separate distance convention.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} {r : ℕ} {S : Finset (Sym2 V)}

/-- A terminal assignment can be extended across an independent buffer.

The special edges are `badEdges G p ∪ S`.  The first constraint prescribes their
new equality pattern; the second makes the flip `q ^^ p` constant on terminals
joined by a walk of length at most `2 * r + 4` avoiding the special edges.
The resulting mask has bad-edge set exactly `S`, and every removed vertex is
outside the radius-`r + 1` ball about the terminals and inside their
radius-`r + 3` ball.
-/
theorem buffered_recolor_of_terminal_assignment (p q : V → Bool)
    (hS : (S : Set (Sym2 V)) ⊆ G.edgeSet)
    (hqedge : ∀ u v, G.Adj u v → s(u, v) ∈ badEdges G p ∪ S →
      (q u = q v ↔ s(u, v) ∈ S))
    (hqnear : ∀ u ∈ ends (badEdges G p ∪ S), ∀ v ∈ ends (badEdges G p ∪ S),
      Near (G.deleteEdges ((badEdges G p ∪ S) : Set (Sym2 V))) {v} (2 * r + 4) u →
        (q u ^^ p u) = (q v ^^ p v)) :
    ∃ Z : Set V, ∃ p' : V → Bool,
      Independent G Z ∧ badEdges (mask G Z) p' = S ∧
        (∀ z ∈ Z, ¬ Near G (ends (badEdges G p ∪ S) : Set V) (r + 1) z) ∧
        (∀ z ∈ Z, Near G (ends (badEdges G p ∪ S) : Set V) (r + 3) z) := by
  classical
  let U := badEdges G p ∪ S
  let W := ends U
  let P := G.deleteEdges (U : Set (Sym2 V))
  let X : Set V := {w | w ∈ W ∧ q w ≠ p w}
  let A (i : ℕ) (v : V) : Prop := Near P X i v
  let Z : Set V := {v | p v = true ∧ A (r + 3) v ∧ ¬ A (r + 1) v}
  let p' (v : V) : Bool := if A (r + 2) v then !p v else p v

  -- Every old bad edge was deleted, so `p` is proper on `P`.
  have hPproper : ∀ ⦃u v⦄, P.Adj u v → p u ≠ p v := by
    intro u v huv heq
    obtain ⟨huv, he⟩ := SimpleGraph.deleteEdges_adj.mp huv
    exact he (Finset.mem_union.mpr (Or.inl ((mem_badEdges G p u v).mpr ⟨huv, heq⟩)))

  -- The unflipped terminals cannot reach the flipped terminals within `D`.
  have hYfar (w : V) (hw : w ∈ W) (hqw : q w = p w) : ¬ A (2 * r + 4) w := by
    rintro ⟨x, hx, path, hpath⟩
    have hnear : Near P {x} (2 * r + 4) w := near_singleton_iff.mpr ⟨path, hpath⟩
    have hphase := hqnear w hw x hx.1 (by
      simpa only [P, U, Finset.coe_union] using hnear)
    apply hx.2
    exact Bool.xor_left_inj.mp (show (q x ^^ p x) = (p x ^^ p x) by
      simpa only [hqw, Bool.xor_self] using hphase.symm)

  -- First-hit invariance transfers any short route to the terminals into `P`.
  have hZfar : ∀ z ∈ Z, ¬ Near G (W : Set V) (r + 1) z := by
    intro z hz hn
    have hnP : Near P (W : Set V) (r + 1) z :=
      (near_deleteEdges_iff (G := G) (U := U) (Set.Subset.refl _)).mpr hn
    obtain ⟨w, hw, path, hpath⟩ := hnP
    by_cases hqw : q w = p w
    · have hwX : Near P X ((r + 3) + path.length) w :=
        near_along_walk hz.2.1 path
      exact hYfar w hw hqw (near_mono_radius (by omega) hwX)
    · exact hz.2.2 ⟨w, ⟨hw, hqw⟩, path, hpath⟩

  have hWoff (w : V) (hw : w ∈ W) : w ∉ Z := by
    intro hz
    exact hZfar w hz (near_of_mem hw)

  -- All buffer vertices have old color `true`, and no special edge touches them.
  have hZind : Independent G Z := by
    intro u v huv hu hv
    have he : s(u, v) ∉ U := fun he => hWoff u (mem_ends_left he) hu
    have huvP : P.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
    exact hPproper huvP (hu.1.trans hv.1.symm)

  -- Each terminal is in exactly its prescribed phase.
  have hp'W (w : V) (hw : w ∈ W) : p' w = q w := by
    by_cases hqw : q w = p w
    · have hna : ¬ A (r + 2) w := by
        intro ha
        exact hYfar w hw hqw (near_mono_radius (by omega) ha)
      simpa only [p', if_neg hna] using hqw.symm
    · have ha : A (r + 2) w := near_of_mem (show w ∈ X from ⟨hw, hqw⟩)
      simpa only [p', if_pos ha] using (Bool.eq_not_of_ne hqw).symm

  -- A phase-crossing edge has both endpoints in the annulus; its `true`
  -- endpoint lies in the buffer.
  have hcross : ∀ ⦃u v⦄, P.Adj u v → A (r + 2) u → ¬ A (r + 2) v →
      u ∈ Z ∨ v ∈ Z := by
    intro u v huv hu hv
    have hu3 : A (r + 3) u := near_mono_radius (by omega) hu
    have hv3 : A (r + 3) v := near_prepend huv.symm hu
    have hu1 : ¬ A (r + 1) u := fun h => hv (near_prepend huv.symm h)
    have hv1 : ¬ A (r + 1) v := fun h => hv (near_mono_radius (by omega) h)
    by_cases hpu : p u = true
    · exact Or.inl ⟨hpu, hu3, hu1⟩
    · have hpv : p v = true := Bool.eq_true_of_not_eq_false (fun hpv =>
        hPproper huv ((Bool.eq_false_of_not_eq_true hpu).trans hpv.symm))
      exact Or.inr ⟨hpv, hv3, hv1⟩

  have hp'P : ∀ ⦃u v⦄, P.Adj u v → u ∉ Z → v ∉ Z → p' u ≠ p' v := by
    intro u v huv hu hv
    by_cases hau : A (r + 2) u <;> by_cases hav : A (r + 2) v
    · simpa only [p', if_pos hau, if_pos hav, Bool.not_injective.ne_iff] using
        hPproper huv
    · obtain h | h := hcross huv hau hav
      · exact (hu h).elim
      · exact (hv h).elim
    · obtain h | h := hcross huv.symm hav hau
      · exact (hv h).elim
      · exact (hu h).elim
    · simpa only [p', if_neg hau, if_neg hav] using hPproper huv

  -- Both endpoints of every edge in `S` are terminals and survive the mask.
  have hSmask : (S : Set (Sym2 V)) ⊆ (mask G Z).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have heU : s(u, v) ∈ U := Finset.mem_union.mpr (Or.inr he)
      change (mask G Z).Adj u v
      exact ⟨hS he, hWoff u (mem_ends_left heU), hWoff v (mem_ends_right heU)⟩

  have hbad : badEdges (mask G Z) p' = S := by
    apply (badEdges_eq_iff_of_subset hSmask).mpr
    intro u v huv
    by_cases heU : s(u, v) ∈ U
    · rw [hp'W u (mem_ends_left heU), hp'W v (mem_ends_right heU)]
      exact hqedge u v huv.1 heU
    · have huvP : P.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv.1, heU⟩
      have hnS : s(u, v) ∉ S := fun he => heU (Finset.mem_union.mpr (Or.inr he))
      exact iff_of_false (hp'P huvP huv.2.1 huv.2.2) hnS

  refine ⟨Z, p', hZind, hbad, hZfar, ?_⟩
  intro z hz
  exact near_mono_graph (G.deleteEdges_le (U : Set (Sym2 V)))
    (near_mono_set (show X ⊆ (W : Set V) from fun _ hx => hx.1) hz.2.1)

end E74

/-
# A localized independent transversal

The third-color vertices introduced at one stage lie outside a wide buffer about
all the new bad edges.  The inductive correction stays inside that buffer.
Consequently both corrections can use the same third color.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- A sufficiently small hereditary cut budget gives an independent transversal,
localized near the bad edges of any starting assignment. -/
theorem exists_localized_transversal (t : ℕ) :
    ∀ (G : SimpleGraph V) (p : V → Bool), (badEdges G p).card = t →
      SmallCuts G certificateBound →
      ∃ (I : Set V) (p' : V → Bool), Independent G I ∧ ProperOff G I p' ∧
        ∀ v ∈ I, Near G (ends (badEdges G p) : Set V) (radiusBound t) v := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro G p hcard hG
    by_cases ht0 : t = 0
    · have hempty : badEdges G p = ∅ := Finset.card_eq_zero.mp (hcard.trans ht0)
      refine ⟨∅, p, ?_, ?_, ?_⟩
      · intro u v _ hu _
        exact Set.notMem_empty u hu
      · intro u v huv _ _
        exact (badEdges_eq_empty_iff G p).mp hempty huv
      · intro v hv
        exact (Set.notMem_empty v hv).elim
    by_cases ht1 : t = 1
    · obtain ⟨e, he⟩ := Finset.card_eq_one.mp (hcard.trans ht1)
      induction e using Sym2.inductionOn with
      | hf u v =>
        have he_mem : s(u, v) ∈ badEdges G p := by rw [he]; simp
        refine ⟨{u}, p, ?_, ?_, ?_⟩
        · intro a b hab ha hb
          have ha' : a = u := ha
          have hb' : b = u := hb
          subst a b
          exact G.loopless u hab
        · intro a b hab ha hb hp
          have habmem := (mem_badEdges G p a b).mpr ⟨hab, hp⟩
          rw [he, Finset.mem_singleton] at habmem
          have hu : u ∈ s(a, b) := habmem.symm ▸ Sym2.mem_mk_left u v
          rcases Sym2.mem_iff.mp hu with hua | hub
          · exact ha (by simpa only [Set.mem_singleton_iff] using hua.symm)
          · exact hb (by simpa only [Set.mem_singleton_iff] using hub.symm)
        · intro a ha
          have ha' : a = u := ha
          subst a
          exact near_of_mem (mem_ends_left he_mem)
    have ht : 2 ≤ t := by omega
    obtain ⟨T, hT, hTcard⟩ := exists_shortSupport_of_smallCuts G certificateBound hG
      ht (two_le_lengthBound (by omega)) (le_refl (certificateBound t))
    obtain ⟨S, hS⟩ := exists_minimalSupport G (lengthBound t)
    have hs : S.card < t := (hS.2 T hT).trans_lt hTcard
    have hsF : S.card ≤ (badEdges G p).card := by rw [hcard]; exact hs.le
    let r := radiusBound (t - 1)
    have hlength : 16 * (badEdges G p).card * (r + 2) ≤ lengthBound t := by
      rw [hcard]
      exact le_rfl
    obtain ⟨q, hqedge, hqnear⟩ := exists_terminal_assignment p hS.1 hsF hlength
    obtain ⟨Z, p₁, hZ, hbad, hfar, hnear⟩ :=
      buffered_recolor_of_terminal_assignment p q hS.1.1 hqedge hqnear
    obtain ⟨I, p₂, hI, hproper, hloc⟩ :=
      ih S.card hs (mask G Z) p₁ (by rw [hbad]) (hG.mask Z)
    have hInear : ∀ v ∈ I, Near G (ends S : Set V) r v := by
      intro v hv
      have hn := hloc v hv
      rw [hbad] at hn
      exact near_mono_graph (mask_le G Z)
        (near_mono_radius (radiusBound_le_pred hs) hn)
    have hSW : (ends S : Set V) ⊆ (ends (badEdges G p ∪ S) : Set V) :=
      ends_mono Finset.subset_union_right
    have hIoff : ∀ v ∈ I, v ∉ Z := by
      intro v hv hz
      exact hfar v hz (near_mono_set hSW (near_mono_radius (by omega) (hInear v hv)))
    have hcross : ∀ z ∈ Z, ∀ v ∈ I, ¬ G.Adj z v := by
      intro z hz v hv hadj
      exact hfar z hz (near_mono_set hSW (near_prepend hadj (hInear v hv)))
    refine ⟨Z ∪ I, p₂, ?_, ?_, ?_⟩
    · intro u v huv hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hZ huv hu hv
      · exact hcross u hu v hv huv
      · exact hcross v hv u hu huv.symm
      · exact hI ⟨huv, hIoff u hu, hIoff v hv⟩ hu hv
    · intro u v huv hu hv
      exact hproper ⟨huv, fun hz => hu (Or.inl hz), fun hz => hv (Or.inl hz)⟩
        (fun hi => hu (Or.inr hi)) (fun hi => hv (Or.inr hi))
    · intro v hv
      have hvW : Near G (ends (badEdges G p ∪ S) : Set V) (r + 3) v := by
        rcases hv with hv | hv
        · exact hnear v hv
        · exact near_mono_set hSW (near_mono_radius (by omega) (hInear v hv))
      have hW : ∀ w ∈ (ends (badEdges G p ∪ S) : Set V),
          Near G (ends (badEdges G p) : Set V) (S.card * lengthBound t) w := by
        intro w hw
        rw [ends_union, Finset.mem_coe, Finset.mem_union] at hw
        rcases hw with hw | hw
        · exact near_of_mem hw
        · exact minimalSupport_near_badEdges hS p w hw
      have hn := near_trans hvW hW
      have hbound := radiusBound_comp hs
      apply near_mono_radius (show (r + 3) + S.card * lengthBound t ≤ radiusBound t by
        dsimp [r]
        omega) hn

/-- The hereditary cut bounds force three colors, uniformly in the number of vertices. -/
theorem finite_colorable_three_of_smallCuts (G : SimpleGraph V)
    (hG : SmallCuts G certificateBound) : G.Colorable 3 := by
  obtain ⟨I, p, hI, hp, _⟩ := exists_localized_transversal
    (badEdges G (fun _ => false)).card G (fun _ => false) rfl hG
  exact colorable_three_of_independent_properOff hI hp

end E74

/-
# From the numerical specification to hereditary small cuts

This module uses only the four distance definitions in `Submission.Spec`.
All minima, bounds, and Boolean cuts needed for the bridge are proved here.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Finite vertex support gives finite ambient edge support, even when `V` is infinite. -/
theorem edgeSet_finite_of_verts_finite (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.Finite := by
  classical
  letI := hA.fintype
  rw [← A.image_coe_edgeSet_coe]
  exact (Set.toFinite A.coe.edgeSet).image _

/-- Deleting every edge always gives a bipartite graph. -/
theorem isBipartite_delete_all_edges (A : G.Subgraph) :
    IsBipartite (A.deleteEdges A.edgeSet).coe := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ ↦ (0 : Fin 2)) ?_⟩
  intro v w h
  exact False.elim (h.2 h.1)

/-- In particular, the set whose infimum defines the distance is nonempty. -/
theorem edgeDistancesToBipartite_nonempty (A : G.Subgraph) :
    (Erdos74.SimpleGraph.edgeDistancesToBipartite A).Nonempty := by
  exact ⟨A.edgeSet.ncard, A.edgeSet, Set.Subset.rfl,
    isBipartite_delete_all_edges A, rfl⟩

/-- The minimum deletion distance of a finite subgraph is attained by a finite edge set. -/
theorem minEdgeDistToBipartite_attained (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ E : Finset (Sym2 V), (E : Set (Sym2 V)) ⊆ A.edgeSet ∧
      IsBipartite (A.deleteEdges (E : Set (Sym2 V))).coe ∧
      E.card = Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  classical
  have hm := Nat.sInf_mem (edgeDistancesToBipartite_nonempty A)
  rcases hm with ⟨E, hE, hb, hc⟩
  have hfin : E.Finite := (edgeSet_finite_of_verts_finite A hA).subset hE
  refine ⟨hfin.toFinset, by simpa using hE, ?_, ?_⟩
  · exact hfin.coe_toFinset.symm ▸ hb
  · rw [← Set.ncard_eq_toFinset_card E hfin]
    exact hc

/-- An ambient edge set with `n` vertices has at most `n.choose 2` edges. -/
theorem subgraph_edgeSet_ncard_le_choose (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.ncard ≤ A.verts.ncard.choose 2 := by
  classical
  letI := hA.fintype
  have he : A.edgeSet.ncard = A.coe.edgeFinset.card := by
    rw [← A.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    exact Set.ncard_eq_toFinset_card' _
  have hv : A.verts.ncard = Fintype.card A.verts := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [he, hv]
  exact A.coe.card_edgeFinset_le_card_choose_two

/-- A uniform bound on all finite-subgraph deletion distances. -/
theorem minEdgeDistToBipartite_le_choose (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.verts.ncard.choose 2 := by
  have hle : Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.edgeSet.ncard :=
    Nat.sInf_le ⟨A.edgeSet, Set.Subset.rfl, isBipartite_delete_all_edges A, rfl⟩
  exact hle.trans (subgraph_edgeSet_ncard_le_choose A hA)

/-- The set defining the supremum at each fixed vertex count is bounded above. -/
theorem subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨A, hcard, hfin, rfl⟩
  simpa [hcard] using minEdgeDistToBipartite_le_choose A hfin

/-- Each finite subgraph's minimum is at most the specification's maximum at its order. -/
theorem minEdgeDistToBipartite_le_max (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤
      Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G A.verts.ncard := by
  exact le_csSup (subgraphEdgeDistsToBipartite_bddAbove G A.verts.ncard)
    ⟨A, rfl, hA, rfl⟩

/-- A bound from `Spec` supplies an actual finite edge-deletion budget for every finite subgraph. -/
theorem edgeDeletionBudget (G : SimpleGraph V) (f : ℕ → ℕ)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ E : Finset (Sym2 V), (E : Set (Sym2 V)) ⊆ A.edgeSet ∧
      IsBipartite (A.deleteEdges (E : Set (Sym2 V))).coe ∧
      E.card ≤ f A.verts.ncard := by
  obtain ⟨E, hE, hb, hc⟩ := minEdgeDistToBipartite_attained A hA
  refine ⟨E, hE, hb, ?_⟩
  rw [hc]
  exact (minEdgeDistToBipartite_le_max A hA).trans (hG A.verts.ncard)

/-- A coloring after edge deletion extends to a Boolean cut of the full ambient type.
Every monochromatic edge of the original subgraph belongs to the deleted set. -/
theorem exists_boolCut_of_deleteEdges_isBipartite (A : G.Subgraph)
    (E : Set (Sym2 V)) (hb : IsBipartite (A.deleteEdges E).coe) :
    ∃ p : V → Bool, ∀ ⦃u v : V⦄, A.Adj u v → p u = p v → s(u, v) ∈ E := by
  classical
  let c : (A.deleteEdges E).coe.Coloring Bool := hb.toColoring (by decide)
  let p : V → Bool := fun v ↦ if hv : v ∈ A.verts then c ⟨v, hv⟩ else false
  refine ⟨p, ?_⟩
  intro u v huv hp
  by_contra he
  have hu : u ∈ A.verts := A.edge_vert huv
  have hv : v ∈ A.verts := A.edge_vert huv.symm
  have hadj : (A.deleteEdges E).coe.Adj ⟨u, hu⟩ ⟨v, hv⟩ := ⟨huv, he⟩
  apply c.valid hadj
  simpa only [p, dif_pos hu, dif_pos hv] using hp

/-- Restrict an ambient cut to a finite subgraph's vertex type.  The injective map on
unordered vertex pairs ensures that no extra bad edges are counted after restriction. -/
theorem coeSubgraph_cut_of_deleteEdges_isBipartite (A : G.Subgraph) [Fintype A.verts]
    (H : A.coe.Subgraph) (E : Finset (Sym2 V))
    (hb : IsBipartite ((Subgraph.coeSubgraph H).deleteEdges (E : Set (Sym2 V))).coe) :
    ∃ p : A.verts → Bool, (badEdges H.spanningCoe p).card ≤ E.card := by
  classical
  obtain ⟨p, hp⟩ := exists_boolCut_of_deleteEdges_isBipartite
    (Subgraph.coeSubgraph H) (E : Set (Sym2 V)) hb
  refine ⟨fun v ↦ p v, ?_⟩
  apply Finset.card_le_card_of_injOn (Sym2.map (Subtype.val : A.verts → V))
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨huv, heq⟩ := (mem_badEdges H.spanningCoe (fun v ↦ p v) u v).mp he
      change s((u : V), (v : V)) ∈ E
      apply hp ?_ heq
      exact (Subgraph.coeSubgraph_adj H u v).mpr ⟨u.property, v.property, huv⟩
  · exact (Sym2.map.injective Subtype.val_injective).injOn

/-- The parametric bridge from `Spec`'s numerical bound to `E74.SmallCuts` on every
finite subgraph.  No finiteness assumption is imposed on the ambient vertex type. -/
theorem smallCuts_of_maxSubgraphEdgeDistToBipartite (B f : ℕ → ℕ)
    (hf : ∀ k, 2 ≤ k → ∀ n, n ≤ B k → f n < k)
    (G : SimpleGraph V)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    letI := hA.fintype
    SmallCuts A.coe B := by
  classical
  letI := hA.fintype
  intro k hk H hH
  have hfin : (Subgraph.coeSubgraph H).verts.Finite :=
    (Set.toFinite H.verts).image (Subtype.val : A.verts → V)
  have hn : (Subgraph.coeSubgraph H).verts.ncard = H.verts.ncard :=
    Set.ncard_image_of_injective H.verts Subtype.val_injective
  obtain ⟨E, _, hb, hcard⟩ := edgeDeletionBudget G f hG (Subgraph.coeSubgraph H) hfin
  obtain ⟨p, hp⟩ := coeSubgraph_cut_of_deleteEdges_isBipartite A H E hb
  refine ⟨p, hp.trans_lt ?_⟩
  rw [hn] at hcard
  exact hcard.trans_lt (hf k hk H.verts.ncard hH)

end E74

open Filter SimpleGraph

namespace E74

universe u

/-- The explicit slowly divergent budget forces a three-coloring even on an
arbitrary infinite vertex type, by finite-subgraph compactness. -/
theorem colorable_three_of_budget {V : Type u} (G : SimpleGraph V)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ budget n) :
    G.Colorable 3 := by
  classical
  apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
  intro A hA
  letI := hA.fintype
  have hsmall : SmallCuts A.coe certificateBound :=
    smallCuts_of_maxSubgraphEdgeDistToBipartite certificateBound budget
      (fun k hk n hn => budget_lt (by omega) hn) G hG A hA
  exact (finite_colorable_three_of_smallCuts A.coe hsmall).some

/-- A sufficiently slow divergent budget is incompatible with infinite
chromatic number. -/
theorem disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) := by
  intro h
  obtain ⟨V, G, htop, hbudget⟩ := h budget budget_tendsto_atTop
  have hthree := colorable_three_of_budget G hbudget
  exact (SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨3, hthree⟩) htop

end E74

theorem Erdos74.erdos_74.disproof : ¬ (type_of% @Erdos74.erdos_74) := by
  exact E74.disproof
