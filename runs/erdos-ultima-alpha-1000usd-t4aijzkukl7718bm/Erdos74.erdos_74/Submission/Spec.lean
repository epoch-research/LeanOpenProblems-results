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


lemma delete_all_edges_bipartite {G : SimpleGraph V} (A : G.Subgraph) :
    (A.deleteEdges A.edgeSet).coe.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
  intro v w h
  exact (h.2 h.1).elim

lemma edge_distances_nonempty {G : SimpleGraph V} (A : G.Subgraph) :
    (SimpleGraph.edgeDistancesToBipartite A).Nonempty := by
  exact ⟨A.edgeSet.ncard, A.edgeSet, Set.Subset.rfl, delete_all_edges_bipartite A, rfl⟩

lemma edge_distance_attained {G : SimpleGraph V} (A : G.Subgraph) :
    ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧
      (A.deleteEdges E).coe.IsBipartite ∧ E.ncard = SimpleGraph.minEdgeDistToBipartite A := by
  obtain ⟨E, hE, hb, he⟩ := Nat.sInf_mem (edge_distances_nonempty A)
  exact ⟨E, hE, hb, he⟩

lemma edge_distance_le_edges {G : SimpleGraph V} (A : G.Subgraph) :
    SimpleGraph.minEdgeDistToBipartite A ≤ A.edgeSet.ncard := by
  exact Nat.sInf_le ⟨A.edgeSet, Set.Subset.rfl, delete_all_edges_bipartite A, rfl⟩

lemma finite_edges_of_finite_verts {G : SimpleGraph V} (A : G.Subgraph)
    (hA : A.verts.Finite) : A.edgeSet.Finite := by
  apply Set.Finite.subset ((hA.prod hA).image (fun p : V × V => s(p.1, p.2)))
  intro e he
  induction e using Sym2.ind with
  | h a b => exact ⟨(a,b), ⟨A.edge_vert he, A.edge_vert he.symm⟩, rfl⟩

lemma card_edges_le_sq_verts {G : SimpleGraph V} (A : G.Subgraph)
    (hA : A.verts.Finite) : A.edgeSet.ncard ≤ A.verts.ncard * A.verts.ncard := by
  have hs : A.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' (A.verts ×ˢ A.verts) := by
    intro e he
    induction e using Sym2.ind with
    | h a b => exact ⟨(a,b), ⟨A.edge_vert he, A.edge_vert he.symm⟩, rfl⟩
  exact (Set.ncard_le_ncard hs ((hA.prod hA).image _)).trans
    ((Set.ncard_image_le (hA.prod hA)).trans_eq Set.ncard_prod)

lemma subgraph_distances_bounded (G : SimpleGraph V) (n : ℕ) :
    BddAbove (G.subgraphEdgeDistsToBipartite n) := by
  refine ⟨n * n, ?_⟩
  rintro k ⟨A, hcard, hfin, rfl⟩
  simpa [hcard] using (edge_distance_le_edges A).trans (card_edges_le_sq_verts A hfin)

lemma edge_distance_le_max {G : SimpleGraph V} (A : G.Subgraph)
    (hA : A.verts.Finite) :
    SimpleGraph.minEdgeDistToBipartite A ≤ G.maxSubgraphEdgeDistToBipartite A.verts.ncard := by
  exact le_csSup (subgraph_distances_bounded G _) ⟨A, rfl, hA, rfl⟩

lemma edge_distance_zero_iff {G : SimpleGraph V} (A : G.Subgraph)
    (hA : A.verts.Finite) : SimpleGraph.minEdgeDistToBipartite A = 0 ↔ A.coe.IsBipartite := by
  constructor
  · intro h
    obtain ⟨E, hE, hb, hc⟩ := edge_distance_attained A
    have he : E = ∅ := (Set.ncard_eq_zero (Set.Finite.subset
      (finite_edges_of_finite_verts A hA) hE)).mp (hc.trans h)
    subst E
    have hcoe : (A.deleteEdges ∅).coe = A.coe := by
      ext v w
      simp
    rwa [hcoe] at hb
  · intro h
    apply Nat.eq_zero_of_le_zero
    have hcoe : (A.deleteEdges ∅).coe = A.coe := by
      ext v w
      simp
    exact Nat.sInf_le ⟨∅, Set.empty_subset _, by rwa [hcoe], Set.ncard_empty _⟩

lemma max_distance_bound_iff (G : SimpleGraph V) (f : ℕ → ℕ) :
    (∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) ↔
    (∀ A : G.Subgraph, A.verts.Finite →
      ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧
        E.ncard ≤ f A.verts.ncard ∧ (A.deleteEdges E).coe.IsBipartite) := by
  constructor
  · intro h A hA
    obtain ⟨E, hE, hb, hc⟩ := edge_distance_attained A
    exact ⟨E, hE, hc.le.trans ((edge_distance_le_max A hA).trans (h _)), hb⟩
  · intro h n
    apply (csSup_le_iff' (subgraph_distances_bounded G n)).mpr
    rintro k ⟨A, hc, hA, rfl⟩
    obtain ⟨E, hE, hcard, hb⟩ := h A hA
    have hmin : SimpleGraph.minEdgeDistToBipartite A ≤ E.ncard :=
      Nat.sInf_le ⟨E, hE, hb, rfl⟩
    exact hmin.trans (by simpa [hc] using hcard)

lemma max_distance_le_sq (G : SimpleGraph V) (n : ℕ) :
    G.maxSubgraphEdgeDistToBipartite n ≤ n * n := by
  apply (csSup_le_iff' (subgraph_distances_bounded G n)).mpr
  rintro k ⟨A, hc, hA, rfl⟩
  simpa [hc] using (edge_distance_le_edges A).trans (card_edges_le_sq_verts A hA)

lemma conjecture_for_large_bounds (f : ℕ → ℕ) (hf : ∀ n, n * n ≤ f n) :
    ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n := by
  refine ⟨ULift.{u} ℕ, ⊤, SimpleGraph.chromaticNumber_top_eq_top_of_infinite _, ?_⟩
  intro n
  exact (max_distance_le_sq _ n).trans (hf n)

lemma colorable_of_bipartite_deletion {G : SimpleGraph V} (A : G.Subgraph)
    (E : Set (Sym2 V)) (hE : E.Finite) (hb : (A.deleteEdges E).coe.IsBipartite) :
    A.coe.Colorable (E.ncard + 2) := by
  classical
  let S : Set V := (fun e : Sym2 V => e.out.1) '' E
  have hS : S.Finite := hE.image _
  letI : Fintype S := hS.fintype
  obtain ⟨b⟩ := hb
  have hedge {v w : V} (hv : v ∉ S) (hw : w ∉ S) : s(v,w) ∉ E := by
    intro h
    have hs : (s(v,w) : Sym2 V).out.1 ∈ S := ⟨s(v,w), h, rfl⟩
    have hp := Sym2.out_fst_mem s(v,w)
    rcases Sym2.mem_iff.mp hp with hp | hp
    · exact hv (hp ▸ hs)
    · exact hw (hp ▸ hs)
  let c : A.verts → S ⊕ Fin 2 := fun v =>
    if hv : (v : V) ∈ S then Sum.inl ⟨v, hv⟩ else Sum.inr (b v)
  have hc : A.coe.Coloring (S ⊕ Fin 2) := SimpleGraph.Coloring.mk c (by
    intro v w h
    dsimp [c]
    split_ifs with hv hw hw
    · intro he
      have hsEq : (⟨(v : V), hv⟩ : S) = ⟨(w : V), hw⟩ := Sum.inl.inj he
      have hval : (v : V) = (w : V) := congrArg (fun x : S => (x : V)) hsEq
      exact A.coe.ne_of_adj h (Subtype.ext hval)
    · simp
    · simp
    · intro he
      exact b.valid ⟨h, hedge hv hw⟩ (Sum.inr.inj he))
  apply SimpleGraph.Colorable.mono ?_ (SimpleGraph.Coloring.colorable hc)
  have hcard : S.ncard ≤ E.ncard := Set.ncard_image_le hE
  simpa [Set.ncard_eq_toFinset_card'] using Nat.add_le_add_right hcard 2

lemma colorable_of_bounded_distance {G : SimpleGraph V} (A : G.Subgraph)
    (hA : A.verts.Finite) :
    A.coe.Colorable (SimpleGraph.minEdgeDistToBipartite A + 2) := by
  obtain ⟨E, hE, hb, hc⟩ := edge_distance_attained A
  have hfin : E.Finite := (finite_edges_of_finite_verts A hA).subset hE
  simpa [hc] using colorable_of_bipartite_deletion A E hfin hb

open Set

lemma coloring_compactness (G : SimpleGraph V) (k : ℕ) [NeZero k]
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable k) : G.Colorable k := by
  classical
  let t : Finset V → Set (V → Fin k) := fun s =>
    {c | ∀ v ∈ s, ∀ w ∈ s, G.Adj v w → c v ≠ c w}
  have ht : ∀ s, IsClosed (t s) := by
    intro s
    simp only [t, setOf_forall]
    refine isClosed_iInter fun v => isClosed_iInter fun hv =>
      isClosed_iInter fun w => isClosed_iInter fun hw => isClosed_iInter fun hadj => ?_
    have hc : IsClosed {p : Fin k × Fin k | p.1 ≠ p.2} := isClosed_discrete _
    change IsClosed ((fun c : V → Fin k => (c v, c w)) ⁻¹' {p : Fin k × Fin k | p.1 ≠ p.2})
    exact hc.preimage ((continuous_apply v).prodMk (continuous_apply w))
  have hf : ∀ ss : Finset (Finset V), (⋂ s ∈ ss, t s).Nonempty := by
    intro ss
    let s := ss.biUnion id
    obtain ⟨c⟩ := h s
    let d : V → Fin k := fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0
    refine ⟨d, ?_⟩
    simp only [mem_iInter]
    intro s' hs' v hv w hw hadj
    have hv' : v ∈ s := Finset.mem_biUnion.mpr ⟨s', hs', hv⟩
    have hw' : w ∈ s := Finset.mem_biUnion.mpr ⟨s', hs', hw⟩
    simp only [d, dif_pos hv', dif_pos hw']
    exact c.valid hadj
  obtain ⟨c, hc⟩ := CompactSpace.iInter_nonempty ht hf
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro v w hvw
  exact (mem_iInter.mp hc {v,w}) v (by simp) w (by simp) hvw

lemma finite_chromatic_witness (G : SimpleGraph V) (hG : G.chromaticNumber = ⊤)
    (k : ℕ) [NeZero k] : ∃ s : Finset V, ¬(G.induce (s : Set V)).Colorable k := by
  classical
  by_contra! h
  have hc := (coloring_compactness G k h).chromaticNumber_le
  rw [hG] at hc
  exact (ENat.coe_lt_top k).not_ge hc

lemma colorable_of_uniform_distance_bound (G : SimpleGraph V) (r : ℕ)
    (h : ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ r) : G.Colorable (r + 2) := by
  apply coloring_compactness
  intro s
  rw [SimpleGraph.induce_eq_coe_induce_top]
  let A : G.Subgraph := (⊤ : G.Subgraph).induce (s : Set V)
  have hA : A.verts.Finite := s.finite_toSet
  have hd : SimpleGraph.minEdgeDistToBipartite A ≤ r :=
    (edge_distance_le_max A hA).trans (h _)
  exact SimpleGraph.Colorable.mono (Nat.add_le_add_right hd 2)
    (colorable_of_bounded_distance A hA)

lemma distance_unbounded_of_infinite_chromatic (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) :
    ∀ r : ℕ, ∃ n, r < G.maxSubgraphEdgeDistToBipartite n := by
  intro r
  by_contra! h
  have hc := (colorable_of_uniform_distance_bound G r h).chromaticNumber_le
  rw [hG] at hc
  exact (ENat.coe_lt_top (r + 2)).not_ge hc


open scoped BigOperators

def natGraphSum (Gs : ℕ → SimpleGraph V) : SimpleGraph (ℕ × V) where
  Adj v w := v.1 = w.1 ∧ (Gs v.1).Adj v.2 w.2
  symm := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨h, ha⟩
    dsimp at h
    subst j
    exact ⟨rfl, ha.symm⟩
  loopless := by
    rintro ⟨i,x⟩ ⟨_, ha⟩
    exact (Gs i).loopless x ha

def natGraphSumHom (Gs : ℕ → SimpleGraph V) (i : ℕ) : Gs i →g natGraphSum Gs where
  toFun x := (i,x)
  map_rel' h := ⟨rfl, h⟩

lemma natGraphSum_chromatic_top (Gs : ℕ → SimpleGraph V)
    (hGs : ∀ i, ¬(Gs i).Colorable i) : (natGraphSum Gs).chromaticNumber = ⊤ := by
  by_contra h
  obtain ⟨k, hk⟩ := SimpleGraph.chromaticNumber_ne_top_iff_exists.mp h
  exact hGs k (hk.of_hom (natGraphSumHom Gs k))

def sumComponent {Gs : ℕ → SimpleGraph V} (A : (natGraphSum Gs).Subgraph) (i : ℕ) :
    (Gs i).Subgraph where
  verts := {x | (i,x) ∈ A.verts}
  Adj x y := A.Adj (i,x) (i,y)
  adj_sub h := (A.adj_sub h).2
  edge_vert h := A.edge_vert h
  symm _ _ h := h.symm

lemma sumComponent_finite {Gs : ℕ → SimpleGraph V}
    (A : (natGraphSum Gs).Subgraph) (hA : A.verts.Finite) (i : ℕ) :
    (sumComponent A i).verts.Finite := by
  exact hA.preimage (by intro x hx y hy h; exact (Prod.mk.inj h).2)

lemma sumComponent_card_le {Gs : ℕ → SimpleGraph V}
    (A : (natGraphSum Gs).Subgraph) (hA : A.verts.Finite) (i : ℕ) :
    (sumComponent A i).verts.ncard ≤ A.verts.ncard := by
  apply Set.ncard_le_ncard_of_injOn (f := fun x => (i,x)) (ht := hA)
  · intro x hx
    exact hx
  · intro x hx y hy h
    exact (Prod.mk.inj h).2

lemma ncard_biUnion_finset_le {α β : Type*} (J : Finset α) (E : α → Set β) :
    (⋃ i ∈ J, E i).ncard ≤ ∑ i ∈ J, (E i).ncard := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert hi]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

lemma natGraphSum_budget (Gs : ℕ → SimpleGraph V) (f : ℕ → ℕ) (b : ℕ → ℕ → ℕ)
    (hbmono : ∀ i, Monotone (b i))
    (hbsum : ∀ n (J : Finset ℕ), (∑ i ∈ J, b i n) ≤ f n)
    (hGs : ∀ i n, (Gs i).maxSubgraphEdgeDistToBipartite n ≤ b i n) :
    ∀ n, (natGraphSum Gs).maxSubgraphEdgeDistToBipartite n ≤ f n := by
  classical
  apply (max_distance_bound_iff _ _).mpr
  intro A hA
  have hcomp (i : ℕ) :=
    (max_distance_bound_iff (Gs i) (b i)).mp (hGs i)
      (sumComponent A i) (sumComponent_finite A hA i)
  choose E hE hcard hbp using hcomp
  have hfin (i : ℕ) : (E i).Finite :=
    (finite_edges_of_finite_verts _ (sumComponent_finite A hA i)).subset (hE i)
  let J : Finset ℕ := (hA.image Prod.fst).toFinset
  let L : ℕ → Set (Sym2 (ℕ × V)) :=
    fun i => Sym2.map (fun x => (i,x)) '' E i
  let D : Set (Sym2 (ℕ × V)) := ⋃ i ∈ J, L i
  refine ⟨D, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    obtain ⟨hiJ, e', he', heq⟩ := Set.mem_iUnion.mp hi
    subst e
    induction e' using Sym2.ind with
    | h x y =>
      exact hE i he'
  · calc
      D.ncard ≤ ∑ i ∈ J, (L i).ncard := ncard_biUnion_finset_le J L
      _ ≤ ∑ i ∈ J, b i (sumComponent A i).verts.ncard := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Set.ncard_image_le (hfin i)).trans (hcard i)
      _ ≤ ∑ i ∈ J, b i A.verts.ncard := by
        apply Finset.sum_le_sum
        intro i hi
        exact hbmono i (sumComponent_card_le A hA i)
      _ ≤ f A.verts.ncard := hbsum _ J
  · let c (i : ℕ) := (hbp i).some
    refine ⟨SimpleGraph.Coloring.mk
      (fun v => c v.val.1 ⟨v.val.2, v.property⟩) ?_⟩
    rintro ⟨⟨i,x⟩, hx⟩ ⟨⟨j,y⟩, hy⟩ h
    have hij : i = j := (A.adj_sub h.1).1
    subst j
    apply (c i).valid
    refine ⟨h.1, ?_⟩
    intro he
    apply h.2
    have hiJ : i ∈ J := by
      apply (Set.Finite.mem_toFinset (hA.image Prod.fst)).mpr
      exact ⟨(i,x), hx, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨hiJ, ⟨s(x,y), he, rfl⟩⟩⟩

noncomputable def tailMinimum (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  sInf (f '' Set.Ici n)

lemma tailMinimum_le (f : ℕ → ℕ) (n : ℕ) : tailMinimum f n ≤ f n := by
  exact Nat.sInf_le ⟨n, by simp, rfl⟩

lemma tailMinimum_mono (f : ℕ → ℕ) : Monotone (tailMinimum f) := by
  intro n m hnm
  obtain ⟨k, hk, he⟩ := Nat.sInf_mem
    (show (f '' Set.Ici m).Nonempty from ⟨f m, m, by simp, rfl⟩)
  exact Nat.sInf_le ⟨k, hnm.trans hk, he⟩

lemma tailMinimum_tendsto (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    Tendsto (tailMinimum f) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop] at hf ⊢
  intro b
  obtain ⟨N, hN⟩ := hf b
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨m, hm, he⟩ := Nat.sInf_mem
    (show (f '' Set.Ici n).Nonempty from ⟨f n, n, by simp, rfl⟩)
  exact (hN m (hn.trans hm)).trans_eq he

lemma geometric_budget_range (N K : ℕ) :
    (∑ i ∈ Finset.range K, N / 2 ^ (i + 1)) + N / 2 ^ K ≤ N := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hdiv : N / 2 ^ (K + 1) = (N / 2 ^ K) / 2 := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hh := Nat.div_mul_le_self (N / 2 ^ K) 2
    rw [← hdiv] at hh
    omega

lemma geometric_budget_finset (N : ℕ) (J : Finset ℕ) :
    (∑ i ∈ J, N / 2 ^ (i + 1)) ≤ N := by
  have hJ : J ⊆ Finset.range (J.sup id + 1) := by
    intro i hi
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hJ
    (f := fun i => N / 2 ^ (i + 1)) (by intros; exact Nat.zero_le _)
  have htotal := geometric_budget_range N (J.sup id + 1)
  exact hsum.trans ((Nat.le_add_right _ _).trans htotal)

lemma unbounded_chromatic_from_bounded_witnesses
    (hfinite : ∀ f : ℕ → ℕ, Tendsto f atTop atTop → ∀ k : ℕ,
      ∃ G : SimpleGraph V, ¬G.Colorable k ∧
        ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n)
    (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    ∃ G : SimpleGraph (ℕ × V), G.chromaticNumber = ⊤ ∧
      ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n := by
  classical
  let b : ℕ → ℕ → ℕ := fun i n => tailMinimum f n / 2 ^ (i + 1)
  have hb : ∀ i, Tendsto (b i) atTop atTop := fun i =>
    (Nat.tendsto_div_const_atTop (by positivity)).comp (tailMinimum_tendsto f hf)
  choose Gs hGs hbudget using fun i => hfinite (b i) (hb i) i
  refine ⟨natGraphSum Gs, natGraphSum_chromatic_top Gs hGs, ?_⟩
  apply natGraphSum_budget Gs f b
  · intro i n m hnm
    exact Nat.div_le_div_right (tailMinimum_mono f hnm)
  · intro n J
    exact (geometric_budget_finset (tailMinimum f n) J).trans (tailMinimum_le f n)
  · exact hbudget

lemma cycle_parity {n : ℕ} {x y : Fin (n+3)} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (cycleGraph (n+3)).Adj x y) : x.val % 2 ≠ y.val % 2 := by
  rw [cycleGraph_adj'] at h
  simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at hx hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · rw [Fin.coe_sub_iff_lt.mpr hxy, Fin.sub_val_of_le hxy.le] at h
    have hxl := x.isLt
    have hyl := y.isLt
    have hxy' : x.val < y.val := hxy
    omega
  · subst y
    simp at h
  · rw [Fin.coe_sub_iff_lt.mpr hxy, Fin.sub_val_of_le hxy.le] at h
    have hxl := x.isLt
    have hyl := y.isLt
    have hxy' : y.val < x.val := hxy
    omega

lemma cycle_shift {n : ℕ} (x y a : Fin (n+3))
    (h : (cycleGraph (n+3)).Adj x y) :
    (cycleGraph (n+3)).Adj (x-a) (y-a) := by
  rw [cycleGraph_adj'] at h ⊢
  simpa [sub_sub_sub_cancel_right] using h

lemma cycle_without_vertex_bipartite {n : ℕ}
    (A : (SimpleGraph.cycleGraph (n+3)).Subgraph) (a : Fin (n+3))
    (ha : a ∉ A.verts) : A.coe.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun x => (⟨((x.val-a).val % 2), Nat.mod_lt _ (by omega)⟩ : Fin 2)) ?_⟩
  intro x y h he
  have hx : x.val - a ≠ 0 := by
    intro hh
    have heq : x.val = a := sub_eq_zero.mp hh
    exact ha (heq ▸ x.property)
  have hy : y.val - a ≠ 0 := by
    intro hh
    have heq : y.val = a := sub_eq_zero.mp hh
    exact ha (heq ▸ y.property)
  exact cycle_parity hx hy (cycle_shift _ _ _ (A.adj_sub h)) (Fin.mk.inj he)

lemma cycle_bad_edge {n : ℕ} (x y : Fin (n+3))
    (ha : (SimpleGraph.cycleGraph (n+3)).Adj x y)
    (hc : x.val % 2 = y.val % 2) : s(x,y) = s(0, Fin.last (n+2)) := by
  have hzero (z : Fin (n+3)) (hz : (SimpleGraph.cycleGraph (n+3)).Adj 0 z)
      (hc0 : 0 = z.val % 2) : z = Fin.last (n+2) := by
    have hpos : (0 : Fin (n+3)) < z := Fin.pos_iff_ne_zero.mpr
      ((SimpleGraph.cycleGraph (n+3)).ne_of_adj hz).symm
    rw [SimpleGraph.cycleGraph_adj', Fin.coe_sub_iff_lt.mpr hpos,
      Fin.sub_val_of_le (Fin.zero_le z)] at hz
    simp only [Fin.val_zero] at hz
    have hlt := z.isLt
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  by_cases hx : x = 0
  · subst x
    have hy := hzero y ha (by simpa using hc)
    subst y
    rfl
  by_cases hy : y = 0
  · subst y
    have hx := hzero x ha.symm (by simpa using hc.symm)
    subst x
    exact Sym2.eq_swap
  exact (cycle_parity hx hy ha hc).elim

lemma cycle_distance_le_one {n : ℕ}
    (A : (SimpleGraph.cycleGraph (n+3)).Subgraph) :
    SimpleGraph.minEdgeDistToBipartite A ≤ 1 := by
  let e : Sym2 (Fin (n+3)) := s(0, Fin.last (n+2))
  let E : Set (Sym2 (Fin (n+3))) := A.edgeSet ∩ {e}
  have hb : (A.deleteEdges E).coe.IsBipartite := by
    refine ⟨SimpleGraph.Coloring.mk
      (fun x => (⟨x.val.val % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)) ?_⟩
    intro x y h he
    apply h.2
    refine ⟨h.1, ?_⟩
    exact cycle_bad_edge _ _ (A.adj_sub h.1) (Fin.mk.inj he)
  have hc : E.ncard ≤ 1 := by
    exact (Set.ncard_le_ncard Set.inter_subset_right (Set.finite_singleton e)).trans_eq
      (Set.ncard_singleton _)
  have hd : SimpleGraph.minEdgeDistToBipartite A ≤ E.ncard :=
    Nat.sInf_le ⟨E, Set.inter_subset_left, hb, rfl⟩
  exact hd.trans hc

lemma cycle_profile_bound (n : ℕ) (f : ℕ → ℕ) (hf : 1 ≤ f (n+3)) :
    ∀ m, (SimpleGraph.cycleGraph (n+3)).maxSubgraphEdgeDistToBipartite m ≤ f m := by
  intro m
  apply (csSup_le_iff' (subgraph_distances_bounded _ _)).mpr
  rintro k ⟨A, hc, hA, rfl⟩
  by_cases hfull : A.verts = Set.univ
  · have hn : m = n+3 := by simpa [hfull] using hc.symm
    exact (cycle_distance_le_one A).trans (hn ▸ hf)
  · obtain ⟨a, ha⟩ : ∃ a, a ∉ A.verts := by
      simpa [Set.eq_univ_iff_forall] using hfull
    have hzero := (edge_distance_zero_iff A hA).mpr
      (cycle_without_vertex_bipartite A a ha)
    rw [hzero]
    exact Nat.zero_le _

lemma nonbipartite_finite_witness (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), ¬G.Colorable 2 ∧
      ∀ m, G.maxSubgraphEdgeDistToBipartite m ≤ f m := by
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp hf) 1
  refine ⟨2*N+3, SimpleGraph.cycleGraph (2*N+3), ?_, ?_⟩
  · intro hc
    have hchi := SimpleGraph.chromaticNumber_cycleGraph_of_odd (2*N+3)
      (by omega) (by exact ⟨N+1, by omega⟩)
    have hle := hc.chromaticNumber_le
    rw [hchi] at hle
    norm_num at hle
  · exact cycle_profile_bound (2*N) f (hN _ (by omega))



lemma profile_bound_of_injective_hom {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G →g H)
    (hφ : Function.Injective φ) (f : ℕ → ℕ)
    (hH : ∀ n, H.maxSubgraphEdgeDistToBipartite n ≤ f n) :
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n := by
  classical
  apply (max_distance_bound_iff _ _).mpr
  intro A hA
  have hmapfin : (A.map φ).verts.Finite := hA.image φ
  obtain ⟨E', hE', hcard', hb'⟩ := (max_distance_bound_iff H f).mp hH (A.map φ) hmapfin
  have hefin : E'.Finite := (finite_edges_of_finite_verts (A.map φ) hmapfin).subset hE'
  let E := A.edgeSet ∩ (Sym2.map φ) ⁻¹' E'
  have hcard : E.ncard ≤ E'.ncard :=
    Set.ncard_le_ncard_of_injOn (Sym2.map φ) (fun _ h => h.2)
      (Sym2.map.injective hφ).injOn hefin
  refine ⟨E, Set.inter_subset_left, ?_, ?_⟩
  · apply hcard.trans
    simpa only [SimpleGraph.Subgraph.map_verts, Set.ncard_image_of_injective _ hφ] using hcard'
  · obtain ⟨c⟩ := hb'
    refine ⟨SimpleGraph.Coloring.mk
      (fun v => c ⟨φ v.val, ⟨v.val, v.property, rfl⟩⟩) ?_⟩
    intro v w h he
    apply c.valid ?_ he
    refine ⟨⟨v.val, w.val, h.1, rfl, rfl⟩, ?_⟩
    intro hh
    exact h.2 ⟨h.1, hh⟩

lemma profile_bound_map {W : Type v} (G : SimpleGraph V) (φ : V ↪ W)
    (f : ℕ → ℕ) (hf : Monotone f)
    (hG : ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) :
    ∀ n, (G.map φ).maxSubgraphEdgeDistToBipartite n ≤ f n := by
  classical
  apply (max_distance_bound_iff _ _).mpr
  intro A hA
  let ψ : G →g G.map φ := (SimpleGraph.Embedding.map φ G).toHom
  let B : G.Subgraph := A.comap ψ
  have hB : B.verts.Finite := hA.preimage φ.injective.injOn
  have hBcard : B.verts.ncard ≤ A.verts.ncard :=
    Set.ncard_le_ncard_of_injOn φ (fun x hx => hx) φ.injective.injOn hA
  obtain ⟨E, hE, hcard, hb⟩ := (max_distance_bound_iff G f).mp hG B hB
  have hEfin : E.Finite := (finite_edges_of_finite_verts B hB).subset hE
  let D := Sym2.map φ '' E
  refine ⟨D, ?_, ?_, ?_⟩
  · rintro e ⟨e', he', rfl⟩
    induction e' using Sym2.ind with
    | h x y => exact (hE he').2
  · exact (Set.ncard_image_le hEfin).trans (hcard.trans (hf hBcard))
  · obtain ⟨c⟩ := hb
    let cs : V → Fin 2 := fun x => if hx : φ x ∈ A.verts then c ⟨x,hx⟩ else 0
    let ct : W → Fin 2 := Function.extend φ cs (fun _ => 0)
    refine ⟨SimpleGraph.Coloring.mk (fun v => ct v.val) ?_⟩
    intro v w h he
    obtain ⟨x, y, hxy, hx, hy⟩ := A.adj_sub h.1
    have hxA : φ x ∈ A.verts := hx.symm ▸ v.property
    have hyA : φ y ∈ A.verts := hy.symm ▸ w.property
    have hxcol : ct v.val = c ⟨x,hxA⟩ := by
      rw [← hx]
      simp only [ct, φ.injective.extend_apply, cs, dif_pos hxA]
    have hycol : ct w.val = c ⟨y,hyA⟩ := by
      rw [← hy]
      simp only [ct, φ.injective.extend_apply, cs, dif_pos hyA]
    change ct v.val = ct w.val at he
    rw [hxcol, hycol] at he
    apply c.valid ?_ he
    refine ⟨⟨hxy, ?_⟩, ?_⟩
    · change A.Adj (φ x) (φ y)
      simpa only [hx, hy] using h.1
    · intro he'
      apply h.2
      exact ⟨s(x,y), he', by simp only [Sym2.map_pair_eq, hx, hy]⟩

lemma nonbipartite_common_type_witness (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    ∃ G : SimpleGraph (ULift.{u} ℕ), ¬G.Colorable 2 ∧
      ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n := by
  classical
  obtain ⟨n, G, hχ, hG⟩ := nonbipartite_finite_witness
    (tailMinimum f) (tailMinimum_tendsto f hf)
  let φ : Fin n ↪ ULift.{u} ℕ :=
    ⟨fun x => ⟨x.val⟩, by intro x y h; exact Fin.ext (congrArg ULift.down h)⟩
  refine ⟨G.map φ, ?_, ?_⟩
  · intro h
    exact hχ (h.of_hom (SimpleGraph.Embedding.map φ G).toHom)
  · intro m
    exact (profile_bound_map G φ _ (tailMinimum_mono f) hG m).trans (tailMinimum_le f m)

def FiniteWitnessProperty : Prop :=
  ∀ f : ℕ → ℕ, Tendsto f atTop atTop → ∀ k : ℕ,
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), ¬G.Colorable k ∧
      ∀ m, G.maxSubgraphEdgeDistToBipartite m ≤ f m

lemma conjecture_of_finite_witness_property (h : FiniteWitnessProperty) :
    ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n := by
  classical
  have hcommon : ∀ f : ℕ → ℕ, Tendsto f atTop atTop → ∀ k : ℕ,
      ∃ G : SimpleGraph (ULift.{u} ℕ), ¬G.Colorable k ∧
        ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n := by
    intro f hf k
    obtain ⟨n, G, hχ, hG⟩ := h (tailMinimum f) (tailMinimum_tendsto f hf) k
    let φ : Fin n ↪ ULift.{u} ℕ :=
      ⟨fun x => ⟨x.val⟩, by intro x y he; exact Fin.ext (congrArg ULift.down he)⟩
    refine ⟨G.map φ, ?_, ?_⟩
    · intro hc
      exact hχ (hc.of_hom (SimpleGraph.Embedding.map φ G).toHom)
    · intro m
      exact (profile_bound_map G φ _ (tailMinimum_mono f) hG m).trans (tailMinimum_le f m)
  intro f hf
  obtain ⟨G, hχ, hG⟩ := unbounded_chromatic_from_bounded_witnesses hcommon f hf
  exact ⟨ℕ × ULift.{u} ℕ, G, hχ, hG⟩

lemma finite_witness_property_of_conjecture
    (h : ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) : FiniteWitnessProperty := by
  classical
  intro f hf k
  obtain ⟨W, G, hχ, hG⟩ := h (tailMinimum f) (tailMinimum_tendsto f hf)
  obtain ⟨s, hs⟩ := finite_chromatic_witness G hχ (k+1)
  let H := G.induce (s : Set W)
  let φ : H ↪g G := SimpleGraph.Embedding.induce (s : Set W)
  have hH : ∀ n, H.maxSubgraphEdgeDistToBipartite n ≤ tailMinimum f n :=
    profile_bound_of_injective_hom φ.toHom φ.injective _ hG
  let e : (s : Set W) ≃ Fin (Fintype.card (s : Set W)) := Fintype.equivFin _
  refine ⟨Fintype.card (s : Set W), H.map e.toEmbedding, ?_, ?_⟩
  · intro hc
    apply hs
    exact SimpleGraph.Colorable.mono (Nat.le_succ k)
      (hc.of_hom (SimpleGraph.Embedding.map e.toEmbedding H).toHom)
  · intro n
    exact (profile_bound_map H e.toEmbedding _ (tailMinimum_mono f) hH n).trans
      (tailMinimum_le f n)

lemma conjecture_iff_finite_witness_property :
    (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) ↔ FiniteWitnessProperty :=
  ⟨finite_witness_property_of_conjecture, conjecture_of_finite_witness_property⟩


lemma colorable_three_of_bipartite_deletion_endpoints
    {G : SimpleGraph V} (E : Set (Sym2 V)) (S : Set V)
    (hends : ∀ v w, s(v,w) ∈ E → v ∈ S ∧ w ∈ S)
    (hcut : (G.deleteEdges E).IsBipartite)
    (hS : (G.induce S).IsBipartite) : G.Colorable 3 := by
  classical
  obtain ⟨b⟩ := hcut
  obtain ⟨c⟩ := hS
  let T : Set V := {v | ∃ hv : v ∈ S, c ⟨v, hv⟩ = 0}
  have hTind : ∀ v ∈ T, ∀ w ∈ T, ¬G.Adj v w := by
    rintro v ⟨hv, hcv⟩ w ⟨hw, hcw⟩ hadj
    exact c.valid (show (G.induce S).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hadj)
      (hcv.trans hcw.symm)
  have hcover : ∀ v w, G.Adj v w → s(v,w) ∈ E → v ∈ T ∨ w ∈ T := by
    intro v w hadj he
    obtain ⟨hv, hw⟩ := hends v w he
    have hne := c.valid (show (G.induce S).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hadj)
    by_cases hc : c ⟨v,hv⟩ = 0
    · exact Or.inl ⟨hv,hc⟩
    · right
      refine ⟨hw, ?_⟩
      have hvlt := (c ⟨v,hv⟩).isLt
      have hwlt := (c ⟨w,hw⟩).isLt
      apply Fin.ext
      have hcv : (c ⟨v,hv⟩).val ≠ 0 := by
        intro h
        apply hc
        exact Fin.ext h
      have hval : (c ⟨v,hv⟩).val ≠ (c ⟨w,hw⟩).val := by
        intro h
        exact hne (Fin.ext h)
      simp only [Fin.val_zero]
      omega
  let d : V → Fin 3 := fun v => if v ∈ T then 2 else (b v).castSucc
  refine ⟨SimpleGraph.Coloring.mk d ?_⟩
  intro v w hadj
  dsimp [d]
  split_ifs with hv hw hw
  · exact (hTind v hv w hw hadj).elim
  · intro he
    have hval := congrArg Fin.val he
    have hwlt := (b w).isLt
    norm_num [Fin.val_castSucc] at hval
    omega
  · intro he
    have hval := congrArg Fin.val he
    have hvlt := (b v).isLt
    norm_num [Fin.val_castSucc] at hval
    omega
  · intro he
    apply b.valid ?_ (Fin.castSucc_inj.mp he)
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hadj, ?_⟩
    intro h
    exact (hcover v w hadj h).elim hv hw


lemma nonbipartite_small_induced_of_deletion
    {G : SimpleGraph V} (hχ : ¬G.Colorable 3)
    (E : Set (Sym2 V)) (hE : E.Finite) (hb : (G.deleteEdges E).IsBipartite) :
    ∃ S : Set V, S.Finite ∧ S.ncard ≤ 2 * E.ncard ∧ ¬(G.induce S).IsBipartite := by
  classical
  let S : Set V := (fun e : Sym2 V => e.out.1) '' E ∪
    (fun e : Sym2 V => e.out.2) '' E
  have hS : S.Finite := (hE.image _).union (hE.image _)
  have hends : ∀ v w, s(v,w) ∈ E → v ∈ S ∧ w ∈ S := by
    intro v w he
    have hm : ∀ x, x ∈ (s(v,w) : Sym2 V) → x ∈ S := by
      intro x hx
      have hp : s((s(v,w) : Sym2 V).out.1, (s(v,w) : Sym2 V).out.2) =
          (s(v,w) : Sym2 V) := Quot.out_eq _
      rw [← hp] at hx
      rcases Sym2.mem_iff.mp hx with hx | hx
      · exact Or.inl ⟨s(v,w), he, hx.symm⟩
      · exact Or.inr ⟨s(v,w), he, hx.symm⟩
    exact ⟨hm v (by simp), hm w (by simp)⟩
  refine ⟨S, hS, ?_, ?_⟩
  · exact (Set.ncard_union_le _ _).trans (by
      have h1 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.1) hE
      have h2 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.2) hE
      omega)
  · intro h
    exact hχ (colorable_three_of_bipartite_deletion_endpoints E S hends hb h)


lemma nonbipartite_small_induced_of_distance {G : SimpleGraph V} (A : G.Subgraph)
    (hA : A.verts.Finite) (hχ : ¬A.coe.Colorable 3) :
    ∃ S : Set A.verts, S.Finite ∧
      S.ncard ≤ 2 * SimpleGraph.minEdgeDistToBipartite A ∧
      ¬(A.coe.induce S).IsBipartite := by
  classical
  obtain ⟨E, hE, hb, hc⟩ := edge_distance_attained A
  have hfin : E.Finite := (finite_edges_of_finite_verts A hA).subset hE
  let E' : Set (Sym2 A.verts) := Sym2.map Subtype.val ⁻¹' E
  have hinj : Function.Injective (Sym2.map (Subtype.val : A.verts → V)) :=
    Sym2.map.injective Subtype.val_injective
  have hfin' : E'.Finite := hfin.preimage (fun x _ y _ h => hinj h)
  have hcard : E'.ncard ≤ E.ncard := Set.ncard_le_ncard_of_injOn
    (Sym2.map Subtype.val) (fun _ h => h) (fun _ _ _ _ h => hinj h) (ht := hfin)
  rw [SimpleGraph.Subgraph.coe_deleteEdges_eq] at hb
  obtain ⟨S, hS, hbound, hnon⟩ :=
    nonbipartite_small_induced_of_deletion hχ E' hfin' hb
  refine ⟨S, hS, ?_, hnon⟩
  exact hbound.trans (Nat.mul_le_mul_left 2 (hcard.trans_eq hc))


lemma sparse_three_coloring_of_bipartite_deletion_endpoints
    {G : SimpleGraph V} (E : Set (Sym2 V)) (S : Set V)
    (hends : ∀ v w, s(v,w) ∈ E → v ∈ S ∧ w ∈ S)
    (hcut : (G.deleteEdges E).IsBipartite)
    (hS : (G.induce S).IsBipartite) :
    ∃ d : G.Coloring (Fin 3), {v | d v = 2} ⊆ S := by
  classical
  obtain ⟨b⟩ := hcut
  obtain ⟨c⟩ := hS
  let T : Set V := {v | ∃ hv : v ∈ S, c ⟨v, hv⟩ = 0}
  have hTind : ∀ v ∈ T, ∀ w ∈ T, ¬G.Adj v w := by
    rintro v ⟨hv, hcv⟩ w ⟨hw, hcw⟩ hadj
    exact c.valid (show (G.induce S).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hadj)
      (hcv.trans hcw.symm)
  have hcover : ∀ v w, G.Adj v w → s(v,w) ∈ E → v ∈ T ∨ w ∈ T := by
    intro v w hadj he
    obtain ⟨hv, hw⟩ := hends v w he
    have hne := c.valid (show (G.induce S).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hadj)
    by_cases hc : c ⟨v,hv⟩ = 0
    · exact Or.inl ⟨hv,hc⟩
    · right
      refine ⟨hw, ?_⟩
      have hvlt := (c ⟨v,hv⟩).isLt
      have hwlt := (c ⟨w,hw⟩).isLt
      apply Fin.ext
      have hcv : (c ⟨v,hv⟩).val ≠ 0 := by
        intro h
        apply hc
        exact Fin.ext h
      have hval : (c ⟨v,hv⟩).val ≠ (c ⟨w,hw⟩).val := by
        intro h
        exact hne (Fin.ext h)
      simp only [Fin.val_zero]
      omega
  let d : V → Fin 3 := fun v => if v ∈ T then 2 else (b v).castSucc
  let hd : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk d (by
    intro v w hadj
    dsimp [d]
    split_ifs with hv hw hw
    · exact (hTind v hv w hw hadj).elim
    · intro he
      have hval := congrArg Fin.val he
      have hwlt := (b w).isLt
      norm_num [Fin.val_castSucc] at hval
      omega
    · intro he
      have hval := congrArg Fin.val he
      have hvlt := (b v).isLt
      norm_num [Fin.val_castSucc] at hval
      omega
    · intro he
      apply b.valid ?_ (Fin.castSucc_inj.mp he)
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hadj, ?_⟩
      intro h
      exact (hcover v w hadj h).elim hv hw
  )
  refine ⟨hd, ?_⟩
  intro v hv
  change d v = 2 at hv
  by_cases ht : v ∈ T
  · exact (show ∃ hv : v ∈ S, c ⟨v,hv⟩ = 0 from ht).choose
  · dsimp [d] at hv
    rw [if_neg ht] at hv
    have hval := congrArg Fin.val hv
    have hlt := (b v).isLt
    norm_num [Fin.val_castSucc] at hval
    omega

set_option maxHeartbeats 2000000 in
lemma colorable_three_of_layer_buffer (G : SimpleGraph V)
    (height : V → ℕ) (t : ℕ)
    (b : V → Fin 2) (c : V → Fin 3)
    (hlayer : ∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1)
    (hb : ∀ ⦃v w⦄, G.Adj v w → t ≤ height v → t ≤ height w → b v ≠ b w)
    (hc : ∀ ⦃v w⦄, G.Adj v w → height v ≤ t + 2 → height w ≤ t + 2 → c v ≠ c w)
    (hbuffer : ∀ v, t ≤ height v → height v ≤ t + 2 → c v ≠ 2) :
    G.Colorable 3 := by
  classical
  let d : V → Fin 3 := fun v =>
    if height v ≤ t then c v
    else if height v = t + 1 then
      if c v = (b v).castSucc then (b v).castSucc
      else if b v = 0 then 2 else 0
    else if height v = t + 2 then
      if c v = (b v).castSucc then (b v).castSucc
      else if b v = 0 then 2 else 1
    else (b v).castSucc
  refine ⟨SimpleGraph.Coloring.mk d ?_⟩
  intro v w hadj
  have hnear1 := hlayer hadj
  have hnear2 := hlayer hadj.symm
  have hbc := hb hadj
  have hcc := hc hadj
  have hzv := hbuffer v
  have hzw := hbuffer w
  dsimp [d]
  generalize hbv : b v = bv at hbc ⊢
  generalize hbw : b w = bw at hbc ⊢
  generalize hcv : c v = cv at hcc hzv ⊢
  generalize hcw : c w = cw at hcc hzw ⊢
  clear hlayer hb hc hbuffer d hbv hbw hcv hcw
  fin_cases bv <;> fin_cases bw <;> fin_cases cv <;> fin_cases cw <;>
    norm_num at hbc hcc hzv hzw ⊢ <;>
    (try split_ifs) <;> simp_all <;> omega


lemma exists_empty_three_layer (height : V → ℕ) (S : Set V)
    (hS : S.Finite) (r : ℕ) (hcard : S.ncard ≤ r) :
    ∃ i : Fin (r + 1), ∀ v ∈ S,
      ¬(3 * i.val + 1 ≤ height v ∧ height v ≤ 3 * i.val + 3) := by
  classical
  by_contra! h
  choose v hv hlo hhi using h
  have hinj : Function.Injective v := by
    intro i j hij
    have hi₁ := hlo i
    have hi₂ := hhi i
    have hj₁ := hlo j
    have hj₂ := hhi j
    rw [hij] at hi₁ hi₂
    apply Fin.ext
    omega
  have hbound : (Set.univ : Set (Fin (r+1))).ncard ≤ S.ncard :=
    Set.ncard_le_ncard_of_injOn v (fun i _ => hv i)
      (fun i _ j _ hij => hinj hij) (ht := hS)
  simp only [Set.ncard_univ, Nat.card_fin] at hbound
  omega

lemma colorable_three_of_sparse_third_color (G : SimpleGraph V)
    (height : V → ℕ) (r : ℕ) (b : V → Fin 2) (c : V → Fin 3)
    (hlayer : ∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1)
    (hb : ∀ ⦃v w⦄, G.Adj v w → 1 ≤ height v → 1 ≤ height w → b v ≠ b w)
    (hc : ∀ ⦃v w⦄, G.Adj v w → height v ≤ 3 * r + 3 →
      height w ≤ 3 * r + 3 → c v ≠ c w)
    (hfin : {v | c v = 2}.Finite) (hcard : {v | c v = 2}.ncard ≤ r) :
    G.Colorable 3 := by
  obtain ⟨i, hi⟩ := exists_empty_three_layer height {v | c v = 2} hfin r hcard
  apply colorable_three_of_layer_buffer G height (3 * i.val + 1) b c hlayer
  · intro v w h hv hw
    exact hb h (by omega) (by omega)
  · intro v w h hv hw
    have hil := i.isLt
    exact hc h (by omega) (by omega)
  · intro v hv hlo he
    exact hi v he ⟨hv, by omega⟩



lemma sparse_three_coloring_of_deletion
    {G : SimpleGraph V} (E : Set (Sym2 V)) (hE : E.Finite)
    (hb : (G.deleteEdges E).IsBipartite)
    (hsmall : ∀ S : Set V, S.Finite → S.ncard ≤ 2 * E.ncard →
      (G.induce S).IsBipartite) :
    ∃ c : G.Coloring (Fin 3), {v | c v = 2}.Finite ∧
      {v | c v = 2}.ncard ≤ 2 * E.ncard := by
  classical
  let S : Set V := (fun e : Sym2 V => e.out.1) '' E ∪
    (fun e : Sym2 V => e.out.2) '' E
  have hS : S.Finite := (hE.image _).union (hE.image _)
  have hends : ∀ v w, s(v,w) ∈ E → v ∈ S ∧ w ∈ S := by
    intro v w he
    have hm : ∀ x, x ∈ (s(v,w) : Sym2 V) → x ∈ S := by
      intro x hx
      have hp : s((s(v,w) : Sym2 V).out.1, (s(v,w) : Sym2 V).out.2) =
          (s(v,w) : Sym2 V) := Quot.out_eq _
      rw [← hp] at hx
      rcases Sym2.mem_iff.mp hx with hx | hx
      · exact Or.inl ⟨s(v,w), he, hx.symm⟩
      · exact Or.inr ⟨s(v,w), he, hx.symm⟩
    exact ⟨hm v (by simp), hm w (by simp)⟩
  have hcard : S.ncard ≤ 2 * E.ncard := (Set.ncard_union_le _ _).trans (by
    have h1 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.1) hE
    have h2 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.2) hE
    omega)
  obtain ⟨c, hc⟩ := sparse_three_coloring_of_bipartite_deletion_endpoints
    E S hends hb (hsmall S hS hcard)
  exact ⟨c, hS.subset hc, (Set.ncard_le_ncard hc hS).trans hcard⟩

lemma colorable_three_of_sparse_inner_coloring (G : SimpleGraph V)
    (height : V → ℕ) (r : ℕ) (b : V → Fin 2)
    (hlayer : ∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1)
    (hb : ∀ ⦃v w⦄, G.Adj v w → 1 ≤ height v → 1 ≤ height w → b v ≠ b w)
    (c : (G.induce {v | height v ≤ 3 * r + 3}).Coloring (Fin 3))
    (hfin : {v | c v = 2}.Finite) (hcard : {v | c v = 2}.ncard ≤ r) :
    G.Colorable 3 := by
  classical
  let d : V → Fin 3 := fun v =>
    if hv : height v ≤ 3 * r + 3 then c ⟨v,hv⟩ else 0
  have hset : {v | d v = 2} = Subtype.val '' {v | c v = 2} := by
    ext v
    constructor
    · intro h
      change d v = 2 at h
      by_cases hv : height v ≤ 3 * r + 3
      · exact ⟨⟨v,hv⟩, by simpa only [d, dif_pos hv] using h, rfl⟩
      · simp [d, hv] at h
    · rintro ⟨v, hv, rfl⟩
      have hp : height (v : V) ≤ 3 * r + 3 := v.property
      simpa [d, hp] using hv
  apply colorable_three_of_sparse_third_color G height r b d hlayer hb
  · intro v w h hv hw
    simpa only [d, dif_pos hv, dif_pos hw] using
      c.valid (show (G.induce {v | height v ≤ 3*r+3}).Adj ⟨v,hv⟩ ⟨w,hw⟩ from h)
  · rw [hset]
    exact hfin.image _
  · rw [hset]
    exact (Set.ncard_image_le hfin).trans hcard


lemma colorable_three_of_local_deletion (G : SimpleGraph V)
    (height : V → ℕ) (r : ℕ) (b : V → Fin 2)
    (hlayer : ∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1)
    (hb : ∀ ⦃v w⦄, G.Adj v w → 1 ≤ height v → 1 ≤ height w → b v ≠ b w)
    (hsmall : ∀ S : Set V, S.Finite → S.ncard ≤ 2 * r → (G.induce S).IsBipartite)
    (E : Set (Sym2 {v : V | height v ≤ 3 * (2 * r) + 3}))
    (hE : E.Finite) (hcard : E.ncard ≤ r)
    (hcut : ((G.induce {v | height v ≤ 3 * (2 * r) + 3}).deleteEdges E).IsBipartite) :
    G.Colorable 3 := by
  classical
  let B : Set V := {v | height v ≤ 3 * (2*r) + 3}
  have hloc : ∀ S : Set B, S.Finite → S.ncard ≤ 2 * E.ncard →
      ((G.induce B).induce S).IsBipartite := by
    intro S hS hbound
    have himage : (Subtype.val '' S : Set V).ncard ≤ 2*r :=
      (Set.ncard_image_le hS).trans (hbound.trans (Nat.mul_le_mul_left 2 hcard))
    have hbi := hsmall (Subtype.val '' S) (hS.image _) himage
    let φ : (G.induce B).induce S →g G.induce (Subtype.val '' S) := {
      toFun := fun v => ⟨v.val.val, ⟨v.val, v.property, rfl⟩⟩
      map_rel' := by intro v w h; exact h }
    exact hbi.of_hom φ
  obtain ⟨c, hfin, hc⟩ := sparse_three_coloring_of_deletion E hE hcut hloc
  apply colorable_three_of_sparse_inner_coloring G height (2*r) b hlayer hb c hfin
  exact hc.trans (Nat.mul_le_mul_left 2 hcard)


def hittingWitnessBound (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => L * (hittingWitnessBound L d + 1)

lemma bounded_hitting_witness [DecidableEq α] (P : Finset α → Prop)
    (L d : ℕ) (hsize : ∀ s, P s → s.card ≤ L)
    (hrobust : ∀ t : Finset α, t.card < d →
      ∃ s : Finset α, P s ∧ Disjoint s t) :
    ∃ w : Finset α, w.card ≤ hittingWitnessBound L d ∧
      ∀ t : Finset α, t.card < d →
        ∃ s : Finset α, P s ∧ s ⊆ w ∧ Disjoint s t := by
  classical
  induction d generalizing P with
  | zero =>
      refine ⟨∅, by simp [hittingWitnessBound], ?_⟩
      intro t ht
      omega
  | succ d ih =>
      obtain ⟨s, hs, _⟩ := hrobust ∅ (by simp)
      have haux : ∀ e : s, ∃ w : Finset α,
          w.card ≤ hittingWitnessBound L d ∧
          ∀ t : Finset α, t.card < d →
            ∃ q : Finset α, (P q ∧ e.val ∉ q) ∧ q ⊆ w ∧ Disjoint q t := by
        intro e
        apply ih (fun q => P q ∧ e.val ∉ q)
        · intro q hq
          exact hsize q hq.1
        · intro t ht
          obtain ⟨q, hq, hqt⟩ := hrobust (insert e.val t) (by
            have hc := Finset.card_insert_le e.val t
            omega)
          refine ⟨q, ⟨hq, ?_⟩, ?_⟩
          · exact fun he => Finset.disjoint_left.mp hqt he (by simp)
          · exact hqt.mono_right (Finset.subset_insert _ _)
      choose w hw havoid using haux
      let W := s ∪ Finset.univ.biUnion w
      refine ⟨W, ?_, ?_⟩
      · have hsum : (∑ e : s, (w e).card) ≤ s.card * hittingWitnessBound L d := by
          calc
            (∑ e : s, (w e).card) ≤ ∑ _e : s, hittingWitnessBound L d :=
              Finset.sum_le_sum (fun e _ => hw e)
            _ = s.card * hittingWitnessBound L d := by simp
        have hbi := Finset.card_biUnion_le (s := (Finset.univ : Finset s)) (t := w)
        have hunion := Finset.card_union_le s (Finset.univ.biUnion w)
        have hsl := hsize s hs
        dsimp [W]
        simp only [hittingWitnessBound]
        calc
          (s ∪ Finset.univ.biUnion w).card ≤ s.card + s.card * hittingWitnessBound L d := by omega
          _ = s.card * (hittingWitnessBound L d + 1) := by ring
          _ ≤ L * (hittingWitnessBound L d + 1) := Nat.mul_le_mul_right _ hsl
      · intro t ht
        by_cases hst : Disjoint s t
        · exact ⟨s, hs, Finset.subset_union_left, hst⟩
        · obtain ⟨e, hes, het⟩ := Finset.not_disjoint_iff.mp hst
          have herase : (t.erase e).card < d := by
            rw [Finset.card_erase_of_mem het]
            have hpos : 0 < t.card := Finset.card_pos.mpr ⟨e, het⟩
            omega
          obtain ⟨q, hq, hqw, hqt⟩ := havoid ⟨e,hes⟩ (t.erase e) herase
          refine ⟨q, hq.1, ?_, ?_⟩
          · intro x hx
            apply Finset.mem_union_right
            exact Finset.mem_biUnion.mpr ⟨⟨e,hes⟩, Finset.mem_univ _, hqw hx⟩
          · apply Finset.disjoint_left.mpr
            intro x hx hxt
            by_cases he : x = e
            · exact hq.2 (he ▸ hx)
            · exact Finset.disjoint_left.mp hqt hx (Finset.mem_erase.mpr ⟨he, hxt⟩)


lemma bounded_edge_deletion_witness (G : SimpleGraph V) (L d : ℕ)
    (hrobust : ∀ t : Finset (Sym2 V), t.card < d →
      ∃ q : Finset (Sym2 V), q.card ≤ L ∧ (q : Set (Sym2 V)) ⊆ G.edgeSet ∧
        ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 V))).IsBipartite ∧ Disjoint q t) :
    ∃ A : G.Subgraph, A.verts.Finite ∧
      A.verts.ncard ≤ 2 * hittingWitnessBound L d ∧
      d ≤ SimpleGraph.minEdgeDistToBipartite A := by
  classical
  let P : Finset (Sym2 V) → Prop := fun q =>
    q.card ≤ L ∧ (q : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 V))).IsBipartite
  have hr : ∀ t : Finset (Sym2 V), t.card < d →
      ∃ q, P q ∧ Disjoint q t := by
    intro t ht
    obtain ⟨q, hq, hqG, hqbi, hqt⟩ := hrobust t ht
    exact ⟨q, ⟨hq,hqG,hqbi⟩, hqt⟩
  obtain ⟨W₀, hW₀, havoid⟩ := bounded_hitting_witness P L d (fun q h => h.1) hr
  let W := W₀.filter (· ∈ G.edgeSet)
  have hWG : (W : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hW : W.card ≤ hittingWitnessBound L d := (Finset.card_filter_le _ _).trans hW₀
  let S : Set V := (fun e : Sym2 V => e.out.1) '' (W : Set (Sym2 V)) ∪
    (fun e : Sym2 V => e.out.2) '' (W : Set (Sym2 V))
  have hWfin : (W : Set (Sym2 V)).Finite := W.finite_toSet
  have hS : S.Finite := (hWfin.image _).union (hWfin.image _)
  have hends : ∀ v w, s(v,w) ∈ W → v ∈ S ∧ w ∈ S := by
    intro v w he
    have hm : ∀ x, x ∈ (s(v,w) : Sym2 V) → x ∈ S := by
      intro x hx
      have hp : s((s(v,w) : Sym2 V).out.1, (s(v,w) : Sym2 V).out.2) =
          (s(v,w) : Sym2 V) := Quot.out_eq _
      rw [← hp] at hx
      rcases Sym2.mem_iff.mp hx with hx | hx
      · exact Or.inl ⟨s(v,w), he, hx.symm⟩
      · exact Or.inr ⟨s(v,w), he, hx.symm⟩
    exact ⟨hm v (by simp), hm w (by simp)⟩
  have hScard : S.ncard ≤ 2 * W.card := (Set.ncard_union_le _ _).trans (by
    have h1 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.1) hWfin
    have h2 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.2) hWfin
    rw [Set.ncard_coe_finset] at h1 h2
    omega)
  let A : G.Subgraph := {
    verts := S
    Adj := (SimpleGraph.fromEdgeSet (W : Set (Sym2 V))).Adj
    adj_sub := by
      intro v w h
      exact G.mem_edgeSet.mp (hWG ((SimpleGraph.fromEdgeSet_adj _).mp h).1)
    edge_vert := by
      intro v w h
      exact (hends v w ((SimpleGraph.fromEdgeSet_adj _).mp h).1).1
    symm := (SimpleGraph.fromEdgeSet (W : Set (Sym2 V))).symm }
  refine ⟨A, hS, hScard.trans (Nat.mul_le_mul_left 2 hW), ?_⟩
  by_contra hnot
  have hlt : SimpleGraph.minEdgeDistToBipartite A < d := Nat.lt_of_not_ge hnot
  obtain ⟨E, hE, hb, he⟩ := edge_distance_attained A
  have hEf : E.Finite := (finite_edges_of_finite_verts A hS).subset hE
  have hEt : hEf.toFinset.card < d := by
    rw [← Set.ncard_eq_toFinset_card E hEf, he]
    exact hlt
  obtain ⟨q, hq, hqW₀, hqE⟩ := havoid hEf.toFinset hEt
  have hqW : q ⊆ W := by
    intro e heq
    exact Finset.mem_filter.mpr ⟨hqW₀ heq, hq.2.1 heq⟩
  obtain ⟨b⟩ := hb
  let c : V → Fin 2 := fun v => if hv : v ∈ S then b ⟨v,hv⟩ else 0
  apply hq.2.2
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro v w h
  obtain ⟨hvw, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
  obtain ⟨hv, hw⟩ := hends v w (hqW hvw)
  dsimp [c]
  rw [dif_pos hv, dif_pos hw]
  apply b.valid
  refine ⟨?_, ?_⟩
  · change (SimpleGraph.fromEdgeSet (W : Set (Sym2 V))).Adj v w
    exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨hqW hvw, hne⟩
  · intro hve
    exact Finset.disjoint_left.mp hqE hvw (hEf.mem_toFinset.mpr hve)


lemma bounded_profile_witness (G : SimpleGraph V) (L d : ℕ)
    (hrobust : ∀ t : Finset (Sym2 V), t.card < d →
      ∃ q : Finset (Sym2 V), q.card ≤ L ∧ (q : Set (Sym2 V)) ⊆ G.edgeSet ∧
        ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 V))).IsBipartite ∧ Disjoint q t) :
    ∃ n ≤ 2 * hittingWitnessBound L d,
      d ≤ G.maxSubgraphEdgeDistToBipartite n := by
  obtain ⟨A, hA, hbound, hd⟩ := bounded_edge_deletion_witness G L d hrobust
  exact ⟨A.verts.ncard, hbound, hd.trans (edge_distance_le_max A hA)⟩


variable {W : Type v}

lemma lift_walk_with_length_bound (G : SimpleGraph V) (H : SimpleGraph W)
    (f : W → V) (C : ℕ)
    (hf : ∀ ⦃a b⦄, H.Adj a b → ∃ p : G.Walk (f a) (f b), p.length ≤ C)
    {a b : W} (p : H.Walk a b) :
    ∃ q : G.Walk (f a) (f b), q.length ≤ C * p.length := by
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | cons h p ih =>
      obtain ⟨q, hq⟩ := hf h
      obtain ⟨r, hr⟩ := ih
      refine ⟨q.append r, ?_⟩
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
      nlinarith

lemma walk_bound_of_finite_roots (G : SimpleGraph V) (S : Set V)
    (hS : S.Finite) (R : ℕ)
    (hcover : ∀ v : V, ∃ a ∈ S, ∃ p : G.Walk a v, p.length ≤ R)
    {u v : V} (huv : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length ≤ (2 * R + 1) * S.ncard + 2 * R := by
  classical
  letI : Fintype S := hS.fintype
  choose a ha p hp using hcover
  let root : V → S := fun v => ⟨a v, ha v⟩
  let K : SimpleGraph S := {
    Adj := fun x y => x ≠ y ∧ ∃ q : G.Walk x.val y.val, q.length ≤ 2*R+1
    symm := by
      intro x y h
      obtain ⟨q, hq⟩ := h.2
      exact ⟨h.1.symm, q.reverse, by simpa using hq⟩
    loopless := by intro x h; exact h.1 rfl }
  have hedge : ∀ {x y : V}, G.Adj x y → K.Reachable (root x) (root y) := by
    intro x y hxy
    by_cases he : root x = root y
    · rw [he]
    · apply SimpleGraph.Adj.reachable
      refine ⟨he, (p x).append (hxy.toWalk.append (p y).reverse), ?_⟩
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        SimpleGraph.Adj.toWalk, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      have hx := hp x
      have hy := hp y
      omega
  have hreach : ∀ {x y : V}, G.Reachable x y → K.Reachable (root x) (root y) := by
    rintro x y ⟨q⟩
    induction q with
    | nil => exact .rfl
    | cons h q ih => exact (hedge h).trans ih
  obtain ⟨q, hq, _⟩ := (hreach huv).exists_path_of_dist
  obtain ⟨z, hz⟩ := lift_walk_with_length_bound G K Subtype.val (2*R+1)
    (fun _ _ h => h.2) q
  have hlen : q.length ≤ S.ncard := by
    have hh := hq.length_lt
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hh
    exact Nat.le_of_lt hh
  refine ⟨(p u).reverse.append (z.append (p v)), ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  have hmul := Nat.mul_le_mul_left (2*R+1) hlen
  have hpu := hp u
  have hpv := hp v
  omega

lemma short_odd_loop_of_walk_bound (G : SimpleGraph V) (D : ℕ)
    (hbound : ∀ ⦃u v⦄, G.Reachable u v → ∃ p : G.Walk u v, p.length ≤ D)
    (hG : ¬G.IsBipartite) :
    ∃ v : V, ∃ p : G.Walk v v, Odd p.length ∧ p.length ≤ 2*D+1 := by
  classical
  let root : V → V := fun v => (G.connectedComponentMk v).out
  have hroot : ∀ v, G.Reachable (root v) v := by
    intro v
    exact SimpleGraph.ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk v))
  let c : V → Fin 2 := fun v => ⟨G.dist (root v) v % 2, Nat.mod_lt _ (by omega)⟩
  have hbad : ∃ u v, G.Adj u v ∧ c u = c v := by
    by_contra! h
    exact hG ⟨SimpleGraph.Coloring.mk c (fun {_ _} hxy => h _ _ hxy)⟩
  obtain ⟨u, v, huv, hsame⟩ := hbad
  have hr : root u = root v := congrArg Quot.out
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv)
  have hrv : G.Reachable (root u) v := (hroot u).trans huv.reachable
  obtain ⟨pu, hpu⟩ := (hroot u).exists_walk_length_eq_dist
  obtain ⟨pv, hpv⟩ := hrv.exists_walk_length_eq_dist
  obtain ⟨qu, hqu⟩ := hbound (hroot u)
  obtain ⟨qv, hqv⟩ := hbound hrv
  have hdu : G.dist (root u) u ≤ D := (SimpleGraph.dist_le qu).trans hqu
  have hdv : G.dist (root u) v ≤ D := (SimpleGraph.dist_le qv).trans hqv
  refine ⟨root u, pu.append (huv.toWalk.append pv.reverse), ?_, ?_⟩
  · apply Nat.odd_iff.mpr
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Adj.toWalk, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hpu, hpv]
    have he := congrArg Fin.val hsame
    change G.dist (root u) u % 2 = G.dist (root v) v % 2 at he
    rw [← hr] at he
    omega
  · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Adj.toWalk, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hpu, hpv]
    omega


lemma finite_edges_of_odd_loop {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : Odd p.length) :
    ∃ q : Finset (Sym2 V), q.card ≤ p.length ∧
      (q : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 V))).IsBipartite := by
  classical
  let q := p.edges.toFinset
  have hqG : (q : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  have hq : q.card ≤ p.length := by
    simpa only [SimpleGraph.Walk.length_edges] using List.toFinset_card_le p.edges
  refine ⟨q, hq, hqG, ?_⟩
  let H := SimpleGraph.fromEdgeSet (q : Set (Sym2 V))
  have hH : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      apply H.mem_edgeSet.mpr
      apply (SimpleGraph.fromEdgeSet_adj _).mpr
      refine ⟨List.mem_toFinset.mpr he, ?_⟩
      exact (G.mem_edgeSet.mp (p.edges_subset_edgeSet he)).ne
  intro hbi
  have hthree := (p.transfer H hH).three_le_chromaticNumber_of_odd_loop (by simpa using hp)
  have htwo := hbi.chromaticNumber_le
  have hbad := hthree.trans htwo
  norm_num at hbad

lemma walk_suffix_after_deletion {G : SimpleGraph V} (E : Set (Sym2 V))
    {u v : V} (p : G.Walk u v) :
    ∃ x : V, (x = u ∨ ∃ y, s(y,x) ∈ E) ∧
      ∃ q : (G.deleteEdges E).Walk x v, q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨_, Or.inl rfl, .nil, by simp⟩
  | @cons u v w huv p ih =>
      obtain ⟨x, hx, q, hq⟩ := ih
      rcases hx with hx | hx
      · subst x
        by_cases he : s(u,v) ∈ E
        · exact ⟨v, Or.inr ⟨u, he⟩, q, by simpa using hq.trans (Nat.le_succ _)⟩
        · refine ⟨u, Or.inl rfl,
            q.cons ((SimpleGraph.deleteEdges_adj).mpr ⟨huv, he⟩), ?_⟩
          simp only [SimpleGraph.Walk.length_cons]
          omega
      · exact ⟨x, Or.inr hx, q, by simpa using hq.trans (Nat.le_succ _)⟩

lemma finite_roots_after_deletion (G : SimpleGraph V) (S : Set V)
    (hS : S.Finite) (R : ℕ)
    (hcover : ∀ v : V, ∃ a ∈ S, ∃ p : G.Walk a v, p.length ≤ R)
    (E : Set (Sym2 V)) (hE : E.Finite) :
    ∃ T : Set V, T.Finite ∧ T.ncard ≤ S.ncard + 2 * E.ncard ∧
      ∀ v : V, ∃ a ∈ T, ∃ p : (G.deleteEdges E).Walk a v, p.length ≤ R := by
  classical
  let U : Set V := (fun e : Sym2 V => e.out.1) '' E ∪
    (fun e : Sym2 V => e.out.2) '' E
  have hU : U.Finite := (hE.image _).union (hE.image _)
  have hUcard : U.ncard ≤ 2 * E.ncard := (Set.ncard_union_le _ _).trans (by
    have h1 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.1) hE
    have h2 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.2) hE
    omega)
  have hends : ∀ x y, s(y,x) ∈ E → x ∈ U := by
    intro x y he
    have hp : s((s(y,x) : Sym2 V).out.1, (s(y,x) : Sym2 V).out.2) =
        (s(y,x) : Sym2 V) := Quot.out_eq _
    have hx : x ∈ (s(y,x) : Sym2 V) := by simp
    rw [← hp] at hx
    rcases Sym2.mem_iff.mp hx with hx | hx
    · exact Or.inl ⟨s(y,x), he, hx.symm⟩
    · exact Or.inr ⟨s(y,x), he, hx.symm⟩
  refine ⟨S ∪ U, hS.union hU, (Set.ncard_union_le _ _).trans (Nat.add_le_add_left hUcard _), ?_⟩
  intro v
  obtain ⟨a, ha, p, hp⟩ := hcover v
  obtain ⟨x, hx, q, hq⟩ := walk_suffix_after_deletion E p
  refine ⟨x, ?_, q, hq.trans hp⟩
  rcases hx with rfl | ⟨y, hy⟩
  · exact Or.inl ha
  · exact Or.inr (hends x y hy)


lemma short_nonbipartite_witness_after_deletion (G : SimpleGraph V) (S : Set V)
    (hS : S.Finite) (R d : ℕ)
    (hcover : ∀ v : V, ∃ a ∈ S, ∃ p : G.Walk a v, p.length ≤ R)
    (E : Finset (Sym2 V)) (hE : E.card ≤ d)
    (hbad : ¬(G.deleteEdges (E : Set (Sym2 V))).IsBipartite) :
    ∃ q : Finset (Sym2 V),
      q.card ≤ 2 * ((2 * R + 1) * (S.ncard + 2*d) + 2*R) + 1 ∧
      (q : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 V))).IsBipartite ∧ Disjoint q E := by
  classical
  obtain ⟨T, hT, hcard, hcov⟩ := finite_roots_after_deletion G S hS R hcover
    (E : Set (Sym2 V)) E.finite_toSet
  obtain ⟨v, p, hp, hlen⟩ := short_odd_loop_of_walk_bound
    (G.deleteEdges (E : Set (Sym2 V))) ((2*R+1)*T.ncard+2*R)
    (fun _ _ h => walk_bound_of_finite_roots _ T hT R hcov h) hbad
  obtain ⟨q, hqcard, hqset, hqbad⟩ := finite_edges_of_odd_loop p hp
  rw [SimpleGraph.edgeSet_deleteEdges] at hqset
  refine ⟨q, ?_, (fun _ h => (hqset h).1), hqbad, ?_⟩
  · rw [Set.ncard_coe_finset] at hcard
    have htotal : T.ncard ≤ S.ncard + 2*d := hcard.trans (by omega)
    have hm := Nat.mul_le_mul_left (2*R+1) htotal
    omega
  · apply Finset.disjoint_left.mpr
    intro e he heE
    exact (hqset he).2 heE


lemma bounded_radius_profile_witness (G : SimpleGraph V) (S : Set V)
    (hS : S.Finite) (R d : ℕ)
    (hcover : ∀ v : V, ∃ a ∈ S, ∃ p : G.Walk a v, p.length ≤ R)
    (hbad : ∀ E : Finset (Sym2 V), E.card < d →
      ¬(G.deleteEdges (E : Set (Sym2 V))).IsBipartite) :
    ∃ n ≤ 2 * hittingWitnessBound
        (2 * ((2 * R + 1) * (S.ncard + 2*d) + 2*R) + 1) d,
      d ≤ G.maxSubgraphEdgeDistToBipartite n := by
  apply bounded_profile_witness
  intro E hE
  exact short_nonbipartite_witness_after_deletion G S hS R d hcover E
    (Nat.le_of_lt hE) (hbad E hE)


lemma delete_short_odd_loops_of_profile_bound (G : SimpleGraph V) (L d : ℕ)
    (hbudget : ∀ n ≤ 2 * hittingWitnessBound L d,
      G.maxSubgraphEdgeDistToBipartite n < d) :
    ∃ E : Finset (Sym2 V), E.card < d ∧
      ∀ v : V, ∀ p : (G.deleteEdges (E : Set (Sym2 V))).Walk v v,
        Odd p.length → L < p.length := by
  classical
  by_contra! h
  have hrobust : ∀ E : Finset (Sym2 V), E.card < d →
      ∃ q : Finset (Sym2 V), q.card ≤ L ∧ (q : Set (Sym2 V)) ⊆ G.edgeSet ∧
        ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 V))).IsBipartite ∧ Disjoint q E := by
    intro E hE
    obtain ⟨v, p, hp, hlen⟩ := h E hE
    obtain ⟨q, hqcard, hqset, hqbad⟩ := finite_edges_of_odd_loop p hp
    rw [SimpleGraph.edgeSet_deleteEdges] at hqset
    refine ⟨q, hqcard.trans hlen, (fun _ hq => (hqset hq).1), hqbad, ?_⟩
    apply Finset.disjoint_left.mpr
    intro e he heE
    exact (hqset he).2 heE
  obtain ⟨n, hn, hd⟩ := bounded_profile_witness G L d hrobust
  exact (hbudget n hn).not_ge hd


/-- A truncated distance to a set, together with the walk witnesses needed below. -/
lemma exists_truncated_root_height (G : SimpleGraph V) (S : Set V) (R : ℕ) :
    ∃ height : V → ℕ,
      (∀ v ∈ S, height v = 0) ∧
      (∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1) ∧
      (∀ v, height v ≤ R → ∃ a ∈ S, ∃ p : G.Walk a v,
        p.length = height v ∧ ∀ x ∈ p.support, height x ≤ R) := by
  classical
  let P : V → ℕ → Prop := fun v n => n = R + 1 ∨
    ∃ a ∈ S, ∃ p : G.Walk a v, p.length = n
  have hex : ∀ v, ∃ n, P v n := fun _ => ⟨R + 1, Or.inl rfl⟩
  let h : V → ℕ := fun v => Nat.find (hex v)
  have hle : ∀ v, h v ≤ R + 1 := fun v => Nat.find_min' (hex v) (Or.inl rfl)
  have hw : ∀ (v a : V), a ∈ S → ∀ (p : G.Walk a v), h v ≤ p.length := by
    intro v a ha p
    exact Nat.find_min' (hex v) (Or.inr ⟨a, ha, p, rfl⟩)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro v hv
    exact Nat.eq_zero_of_le_zero (hw v v hv .nil)
  · intro v w hvw
    rcases Nat.find_spec (hex w) with htop | ⟨a, ha, p, hp⟩
    · change h w = R + 1 at htop
      have hv := hle v
      omega
    · have hh := hw v a ha (p.concat hvw.symm)
      simp only [SimpleGraph.Walk.length_concat] at hh
      change p.length = h w at hp
      omega
  · intro v hv
    rcases Nat.find_spec (hex v) with htop | ⟨a, ha, p, hp⟩
    · change h v = R + 1 at htop
      omega
    · refine ⟨a, ha, p, hp, ?_⟩
      intro x hx
      exact (hw x a ha (p.takeUntil x hx)).trans
        ((p.length_takeUntil_le hx).trans (hp.le.trans hv))

/-- Quantitative localization with an explicit finite root set. -/
lemma bounded_profile_witness_of_bipartite_complement (G : SimpleGraph V)
    (S : Set V) (hS : S.Finite) (r : ℕ)
    (hχ : ¬G.Colorable 3)
    (hb : (G.induce Sᶜ).IsBipartite)
    (hsmall : ∀ T : Set V, T.Finite → T.ncard ≤ 2*r → (G.induce T).IsBipartite) :
    ∃ n ≤ 2 * hittingWitnessBound
      (2 * ((2*(6*r+3)+1)*(S.ncard+2*(r+1))+2*(6*r+3)) + 1) (r+1),
      r+1 ≤ G.maxSubgraphEdgeDistToBipartite n := by
  classical
  let R := 3*(2*r)+3
  obtain ⟨height, hzero, hlayer, hwalk⟩ := exists_truncated_root_height G S R
  let B : Set V := {v | height v ≤ R}
  let K := G.induce B
  let T : Set B := Subtype.val ⁻¹' S
  have hT : T.Finite := hS.preimage Subtype.val_injective.injOn
  have hTcard : T.ncard ≤ S.ncard := Set.ncard_le_ncard_of_injOn
    Subtype.val (fun _ h => h) Subtype.val_injective.injOn (ht := hS)
  have hcov : ∀ v : B, ∃ a ∈ T, ∃ p : K.Walk a v, p.length ≤ R := by
    intro v
    obtain ⟨a, ha, p, hp, hps⟩ := hwalk v.val v.property
    have haB : a ∈ B := by change height a ≤ R; rw [hzero a ha]; omega
    refine ⟨⟨a, haB⟩, ha, p.induce B hps, ?_⟩
    have hlen := congrArg SimpleGraph.Walk.length (p.map_induce (s := B) hps)
    simp only [SimpleGraph.Walk.length_map] at hlen
    exact hlen.le.trans (hp.le.trans v.property)
  obtain ⟨b⟩ := hb
  let c : V → Fin 2 := fun v => if hv : v ∈ Sᶜ then b ⟨v,hv⟩ else 0
  have hc : ∀ ⦃v w⦄, G.Adj v w → 1 ≤ height v → 1 ≤ height w → c v ≠ c w := by
    intro v w hvw hv hw
    have hvS : v ∈ Sᶜ := by intro hvS; have := hzero v hvS; omega
    have hwS : w ∈ Sᶜ := by intro hwS; have := hzero w hwS; omega
    simpa only [c, dif_pos hvS, dif_pos hwS] using
      b.valid (show (G.induce Sᶜ).Adj ⟨v,hvS⟩ ⟨w,hwS⟩ from hvw)
  have hbad : ∀ E : Finset (Sym2 B), E.card < r+1 →
      ¬(K.deleteEdges (E : Set (Sym2 B))).IsBipartite := by
    intro E hE hbE
    apply hχ
    apply colorable_three_of_local_deletion G height r c hlayer hc hsmall
      (E : Set (Sym2 B)) E.finite_toSet
    · simpa only [Set.ncard_coe_finset] using Nat.le_of_lt_succ hE
    · exact hbE
  have hrobust : ∀ E : Finset (Sym2 B), E.card < r+1 →
      ∃ q : Finset (Sym2 B),
        q.card ≤ 2*((2*R+1)*(S.ncard+2*(r+1))+2*R)+1 ∧
        (q : Set (Sym2 B)) ⊆ K.edgeSet ∧
        ¬(SimpleGraph.fromEdgeSet (q : Set (Sym2 B))).IsBipartite ∧ Disjoint q E := by
    intro E hE
    obtain ⟨q, hq, hqset, hqbad, hqdisj⟩ := short_nonbipartite_witness_after_deletion
      K T hT R (r+1) hcov E (Nat.le_of_lt hE) (hbad E hE)
    refine ⟨q, hq.trans ?_, hqset, hqbad, hqdisj⟩
    gcongr
  obtain ⟨n, hn, hd⟩ := bounded_profile_witness K
    (2*((2*R+1)*(S.ncard+2*(r+1))+2*R)+1) (r+1) hrobust
  let φ : K →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  have hprofile := profile_bound_of_injective_hom φ Subtype.val_injective
    (fun m => G.maxSubgraphEdgeDistToBipartite m) (fun _ => le_rfl)
  refine ⟨n, ?_, hd.trans (hprofile n)⟩
  simpa only [R, show 3*(2*r)+3 = 6*r+3 by omega] using hn


lemma hittingWitnessBound_mono_left (d : ℕ) : Monotone (fun L => hittingWitnessBound L d) := by
  induction d with
  | zero => intro a b hab; simp only [hittingWitnessBound, le_refl]
  | succ d ih =>
    intro a b hab
    simp only [hittingWitnessBound]
    exact Nat.mul_le_mul hab (Nat.add_le_add_right (ih hab) 1)

lemma finite_edge_endpoints (E : Set (Sym2 V)) (hE : E.Finite) :
    ∃ S : Set V, S.Finite ∧ S.ncard ≤ 2*E.ncard ∧
      ∀ v w, s(v,w) ∈ E → v ∈ S ∧ w ∈ S := by
  classical
  let S : Set V := (fun e : Sym2 V => e.out.1) '' E ∪
    (fun e : Sym2 V => e.out.2) '' E
  refine ⟨S, (hE.image _).union (hE.image _), ?_, ?_⟩
  · exact (Set.ncard_union_le _ _).trans (by
      have h1 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.1) hE
      have h2 := Set.ncard_image_le (f := fun e : Sym2 V => e.out.2) hE
      omega)
  · intro v w he
    have hm : ∀ x, x ∈ (s(v,w) : Sym2 V) → x ∈ S := by
      intro x hx
      have hp : s((s(v,w) : Sym2 V).out.1, (s(v,w) : Sym2 V).out.2) =
          (s(v,w) : Sym2 V) := Quot.out_eq _
      rw [← hp] at hx
      rcases Sym2.mem_iff.mp hx with hx | hx
      · exact Or.inl ⟨s(v,w), he, hx.symm⟩
      · exact Or.inr ⟨s(v,w), he, hx.symm⟩
    exact ⟨hm v (by simp), hm w (by simp)⟩

/-- The bound still depends on the cardinality `m` of a global bipartizing set. -/
def localObstructionBound (m r : ℕ) : ℕ :=
  2 * hittingWitnessBound
    (2*((2*(6*r+3)+1)*(2*m+2*(r+1))+2*(6*r+3))+1) (r+1)

lemma bounded_profile_witness_of_bipartizing_edges (G : SimpleGraph V)
    (E : Set (Sym2 V)) (hE : E.Finite) (hb : (G.deleteEdges E).IsBipartite)
    (r : ℕ) (hχ : ¬G.Colorable 3)
    (hsmall : ∀ T : Set V, T.Finite → T.ncard ≤ 2*r → (G.induce T).IsBipartite) :
    ∃ n ≤ localObstructionBound E.ncard r,
      r+1 ≤ G.maxSubgraphEdgeDistToBipartite n := by
  classical
  obtain ⟨S, hS, hScard, hends⟩ := finite_edge_endpoints E hE
  have hcomp : (G.induce Sᶜ).IsBipartite := by
    obtain ⟨b⟩ := hb
    refine ⟨SimpleGraph.Coloring.mk (fun v => b v.val) ?_⟩
    intro v w hadj
    apply b.valid
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩
    intro he
    exact v.property (hends v.val w.val he).1
  obtain ⟨n, hn, hd⟩ := bounded_profile_witness_of_bipartite_complement G S hS r hχ hcomp hsmall
  refine ⟨n, hn.trans ?_, hd⟩
  apply Nat.mul_le_mul_left 2
  apply hittingWitnessBound_mono_left
  gcongr


set_option maxHeartbeats 4000000 in
/-- Gluing two three-colorings across a four-layer region where both are binary. -/
lemma glue_three_colorings (G : SimpleGraph V) (height : V → ℕ) (t : ℕ)
    (a b : V → Fin 3)
    (hlayer : ∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1)
    (ha : ∀ ⦃v w⦄, G.Adj v w → height v ≤ t+2 → height w ≤ t+2 → a v ≠ a w)
    (hb : ∀ ⦃v w⦄, G.Adj v w → t ≤ height v → t ≤ height w → b v ≠ b w)
    (hba : ∀ v, t ≤ height v → height v ≤ t+2 → a v ≠ 2)
    (hbb : ∀ v, t ≤ height v → height v ≤ t+3 → b v ≠ 2) :
    ∃ c : G.Coloring (Fin 3), ∀ v, c v = 2 → height v ≤ t+2 ∨ b v = 2 := by
  classical
  let d : V → Fin 3 := fun v =>
    if height v ≤ t then a v
    else if height v = t+1 then
      if a v = b v then b v else if b v = 0 then 2 else 0
    else if height v = t+2 then
      if a v = b v then b v else if b v = 0 then 2 else 1
    else b v
  have hd : ∀ ⦃v w⦄, G.Adj v w → d v ≠ d w := by
    intro v w hadj
    have hnear1 := hlayer hadj
    have hnear2 := hlayer hadj.symm
    have havw := ha hadj
    have hbvw := hb hadj
    have hzav := hba v
    have hzaw := hba w
    have hzbv := hbb v
    have hzbw := hbb w
    dsimp [d]
    generalize hav : a v = av at havw hzav ⊢
    generalize haw : a w = aw at havw hzaw ⊢
    generalize hbv : b v = bv at hbvw hzbv ⊢
    generalize hbw : b w = bw at hbvw hzbw ⊢
    clear hlayer ha hb hba hbb d hav haw hbv hbw
    fin_cases av <;> fin_cases aw <;> fin_cases bv <;> fin_cases bw <;>
      norm_num at havw hbvw hzav hzaw hzbv hzbw ⊢ <;>
      (try split_ifs) <;> simp_all <;> omega
  refine ⟨SimpleGraph.Coloring.mk d (fun {_ _} h => hd h), ?_⟩
  intro v hv
  change d v = 2 at hv
  by_cases h : height v ≤ t+2
  · exact Or.inl h
  · right
    simpa only [d, if_neg (show ¬height v ≤ t by omega),
      if_neg (show height v ≠ t+1 by omega), if_neg (show height v ≠ t+2 by omega)] using hv

lemma exists_empty_four_layer (height : V → ℕ) (S : Set V)
    (hS : S.Finite) (m q : ℕ) (hcard : S.ncard ≤ m) :
    ∃ i : Fin (m+1), ∀ v ∈ S,
      ¬(q+4*i.val+1 ≤ height v ∧ height v ≤ q+4*i.val+4) := by
  classical
  by_contra! h
  choose v hv hlo hhi using h
  have hinj : Function.Injective v := by
    intro i j hij
    have hi₁ := hlo i
    have hi₂ := hhi i
    have hj₁ := hlo j
    have hj₂ := hhi j
    rw [hij] at hi₁ hi₂
    apply Fin.ext
    omega
  have hbound := Set.ncard_le_ncard_of_injOn v (s := Set.univ)
    (fun i _ => hv i) (fun i _ j _ hij => hinj hij) (ht := hS)
  simp only [Set.ncard_univ, Nat.card_fin] at hbound
  omega

lemma height_le_length (G : SimpleGraph V) (height : V → ℕ)
    (hlayer : ∀ ⦃v w⦄, G.Adj v w → height v ≤ height w + 1)
    {u v : V} (p : G.Walk u v) : height v ≤ height u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hh := hlayer h.symm
    simp only [SimpleGraph.Walk.length_cons]
    omega

lemma walk_suffix_of_edge_agreement (G H : SimpleGraph V) (S : Set V)
    (hagree : ∀ ⦃u v⦄, G.Adj u v → H.Adj u v ∨ (u ∈ S ∧ v ∈ S))
    {u v : V} (p : G.Walk u v) :
    ∃ x, (x = u ∨ x ∈ S) ∧ ∃ q : H.Walk x v, q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨_, Or.inl rfl, .nil, by simp⟩
  | @cons u v w huv p ih =>
    obtain ⟨x, hx, q, hq⟩ := ih
    rcases hx with hx | hx
    · subst x
      rcases hagree huv with h | h
      · refine ⟨u, Or.inl rfl, q.cons h, ?_⟩
        simpa only [SimpleGraph.Walk.length_cons] using Nat.add_le_add_right hq 1
      · exact ⟨v, Or.inr h.2, q, by simpa using hq.trans (Nat.le_succ _)⟩
    · exact ⟨x, Or.inr hx, q, by simpa using hq.trans (Nat.le_succ _)⟩

/-- An odd-loop threshold; stable under taking induced subgraphs. -/
def NoShortOddLoops (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∀ v : V, ∀ p : G.Walk v v, Odd p.length → L < p.length

lemma NoShortOddLoops.induce {G : SimpleGraph V} {L : ℕ}
    (h : NoShortOddLoops G L) (S : Set V) : NoShortOddLoops (G.induce S) L := by
  intro v p hp
  simpa only [SimpleGraph.Walk.length_map] using
    h v.val (p.map (SimpleGraph.Embedding.induce S).toHom) (by simpa using hp)

lemma bipartite_induce_of_no_short_odd_loops (G : SimpleGraph V) (L : ℕ)
    (h : NoShortOddLoops G L) (S : Set V) (hS : S.Finite)
    (hsize : 2*S.ncard+1 ≤ L) : (G.induce S).IsBipartite := by
  classical
  letI : Fintype S := hS.fintype
  by_contra hbad
  have hbound : ∀ ⦃v w : S⦄, (G.induce S).Reachable v w →
      ∃ p : (G.induce S).Walk v w, p.length ≤ S.ncard := by
    intro v w hvw
    obtain ⟨p, hp, _⟩ := hvw.exists_path_of_dist
    have hh := hp.length_lt
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hh
    exact ⟨p, Nat.le_of_lt hh⟩
  obtain ⟨v, p, hp, hlen⟩ := short_odd_loop_of_walk_bound (G.induce S) S.ncard hbound hbad
  exact (h.induce S v p hp).not_ge (hlen.trans hsize)

lemma sparse_three_coloring_of_edge_agreement (G H : SimpleGraph V) (S : Set V)
    (hagree : ∀ ⦃u v⦄, G.Adj u v → H.Adj u v ∨ (u ∈ S ∧ v ∈ S))
    (hH : H.IsBipartite) (hS : (G.induce S).IsBipartite) :
    ∃ c : G.Coloring (Fin 3), {v | c v = 2} ⊆ S := by
  let E : Set (Sym2 V) := G.edgeSet \ H.edgeSet
  apply sparse_three_coloring_of_bipartite_deletion_endpoints E S
  · intro u v he
    rcases hagree (G.mem_edgeSet.mp he.1) with h | h
    · exact (he.2 (H.mem_edgeSet.mpr h)).elim
    · exact h
  · apply hH.of_hom
    refine { toFun := id, map_rel' := ?_ }
    intro u v h
    have hh := SimpleGraph.deleteEdges_adj.mp h
    by_contra hn
    exact hh.2 ⟨G.mem_edgeSet.mpr hh.1, fun he => hn (H.mem_edgeSet.mp he)⟩
  · exact hS


def stageRoots (S : ℕ → Set V) : ℕ → Set V
  | 0 => ∅
  | n+1 => stageRoots S n ∪ S n

def stageRadius (n : ℕ) : ℕ := 4*n*(n+2)

def stageLoopBound (n : ℕ) : ℕ :=
  2*((2*stageRadius (n+1)+1)*(n*(n+1))+2*stageRadius (n+1))+4*(n+1)+10

lemma stageRoots_finite_card (n : ℕ) (S : ℕ → Set V)
    (hS : ∀ i < n, (S i).Finite ∧ (S i).ncard ≤ 2*(i+1)) :
    (stageRoots S n).Finite ∧ (stageRoots S n).ncard ≤ n*(n+1) := by
  induction n with
  | zero => simp [stageRoots]
  | succ n ih =>
    obtain ⟨hf, hc⟩ := ih (fun i hi => hS i (by omega))
    obtain ⟨hfn, hcn⟩ := hS n (by omega)
    refine ⟨hf.union hfn, (Set.ncard_union_le _ _).trans ?_⟩
    nlinarith

lemma stageRoots_preimage (S : ℕ → Set V) (f : W → V) (n : ℕ) :
    stageRoots (fun i => f ⁻¹' S i) n = f ⁻¹' stageRoots S n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stageRoots, ih, Set.preimage_union]

lemma stage_edge_agreement (n : ℕ) (Gs : ℕ → SimpleGraph V) (S : ℕ → Set V)
    (h : ∀ i < n, ∀ ⦃u v⦄, (Gs i).Adj u v →
      (Gs (i+1)).Adj u v ∨ (u ∈ S i ∧ v ∈ S i)) :
    ∀ ⦃u v⦄, (Gs 0).Adj u v →
      (Gs n).Adj u v ∨ (u ∈ stageRoots S n ∧ v ∈ stageRoots S n) := by
  induction n with
  | zero => intro u v huv; exact Or.inl huv
  | succ n ih =>
    intro u v huv
    rcases ih (fun i hi => h i (by omega)) huv with hh | hh
    · rcases h n (by omega) hh with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨Or.inr h'.1, Or.inr h'.2⟩
    · exact Or.inr ⟨Or.inl hh.1, Or.inl hh.2⟩

set_option maxHeartbeats 4000000 in
/-- Widely separated odd-cycle scales admit a localized three-coloring. -/
lemma multiscale_sparse_coloring (n : ℕ) (Gs : ℕ → SimpleGraph V) (S : ℕ → Set V)
    (hS : ∀ i < n, (S i).Finite ∧ (S i).ncard ≤ 2*(i+1))
    (hagree : ∀ i < n, ∀ ⦃u v⦄, (Gs i).Adj u v →
      (Gs (i+1)).Adj u v ∨ (u ∈ S i ∧ v ∈ S i))
    (hodd : ∀ i < n, NoShortOddLoops (Gs i) (stageLoopBound i))
    (hfinal : (Gs n).IsBipartite) :
    ∃ c : (Gs 0).Coloring (Fin 3), ∀ v, c v = 2 →
      ∃ a ∈ stageRoots S n, ∃ p : (Gs 0).Walk a v, p.length ≤ stageRadius n := by
  classical
  induction n generalizing V with
  | zero =>
    obtain ⟨b⟩ := hfinal
    refine ⟨SimpleGraph.Coloring.mk (fun v => (b v).castSucc) (fun {_ _} h he =>
      b.valid h (Fin.castSucc_inj.mp he)), ?_⟩
    intro v hv
    change (b v).castSucc = (2 : Fin 3) at hv
    have hval := congrArg Fin.val hv
    have hlt := (b v).isLt
    change (b v).val = 2 at hval
    omega
  | succ n ih =>
    let A := stageRoots S n
    obtain ⟨hA, hAcard⟩ := stageRoots_finite_card n S (fun i hi => hS i (by omega))
    have hdiff := stage_edge_agreement n Gs S (fun i hi => hagree i (by omega))
    let R := stageRadius (n+1)
    have hR : R = stageRadius n + 4*(2*(n+1))+4 := by dsimp [R, stageRadius]; ring
    obtain ⟨height, hzero, hlayer, hwalk⟩ := exists_truncated_root_height (Gs 0) A R
    let B : Set V := {v | height v ≤ R}
    let A' : Set B := Subtype.val ⁻¹' A
    have hA' : A'.Finite := hA.preimage Subtype.val_injective.injOn
    have hA'card : A'.ncard ≤ n*(n+1) :=
      (Set.ncard_le_ncard_of_injOn Subtype.val (fun _ h => h)
        Subtype.val_injective.injOn (ht := hA)).trans hAcard
    have hcov : ∀ v : B, ∃ a ∈ A', ∃ p : ((Gs n).induce B).Walk a v, p.length ≤ R := by
      intro v
      obtain ⟨a, ha, p, hp, hps⟩ := hwalk v.val v.property
      have haB : a ∈ B := by change height a ≤ R; rw [hzero a ha]; omega
      have hdiff' : ∀ ⦃u v : B⦄, ((Gs 0).induce B).Adj u v →
          ((Gs n).induce B).Adj u v ∨ (u ∈ A' ∧ v ∈ A') := by
        intro u v huv
        exact hdiff huv
      obtain ⟨x, hx, q, hq⟩ := walk_suffix_of_edge_agreement
        ((Gs 0).induce B) ((Gs n).induce B) A' hdiff' (p.induce B hps)
      have hlen := congrArg SimpleGraph.Walk.length (p.map_induce (s := B) hps)
      simp only [SimpleGraph.Walk.length_map] at hlen
      refine ⟨x, ?_, q, hq.trans (hlen.le.trans (hp.le.trans v.property))⟩
      rcases hx with rfl | hx
      · exact ha
      · exact hx
    have hbi : ((Gs n).induce B).IsBipartite := by
      by_contra hbad
      obtain ⟨v, p, hp, hlen⟩ := short_odd_loop_of_walk_bound ((Gs n).induce B)
        ((2*R+1)*A'.ncard+2*R)
        (fun _ _ h => walk_bound_of_finite_roots _ A' hA' R hcov h) hbad
      have hlt := (hodd n (by omega)).induce B v p hp
      have hmul := Nat.mul_le_mul_left (2*R+1) hA'card
      dsimp [stageLoopBound] at hlt
      change 2*((2*R+1)*(n*(n+1))+2*R)+4*(n+1)+10 < p.length at hlt
      omega
    have hSi : ∀ i < n, (Subtype.val ⁻¹' S i : Set B).Finite ∧
        (Subtype.val ⁻¹' S i : Set B).ncard ≤ 2*(i+1) := by
      intro i hi
      obtain ⟨hf, hc⟩ := hS i (by omega)
      exact ⟨hf.preimage Subtype.val_injective.injOn,
        (Set.ncard_le_ncard_of_injOn Subtype.val (fun _ h => h)
          Subtype.val_injective.injOn (ht := hf)).trans hc⟩
    obtain ⟨cin, hcin⟩ := ih (fun i => (Gs i).induce B) (fun i => Subtype.val ⁻¹' S i)
      hSi (fun i hi _ _ h => hagree i (by omega) h)
      (fun i hi => (hodd i (by omega)).induce B) hbi
    have hcinheight : ∀ v : B, cin v = 2 → height v.val ≤ stageRadius n := by
      intro v hv
      obtain ⟨a, ha, p, hp⟩ := hcin v hv
      rw [stageRoots_preimage] at ha
      have hh := height_le_length (Gs 0) height hlayer
        (p.map (SimpleGraph.Embedding.induce B).toHom)
      simp only [SimpleGraph.Walk.length_map] at hh
      change height v.val ≤ height a.val + p.length at hh
      rw [hzero a.val ha, zero_add] at hh
      exact hh.trans hp
    obtain ⟨hSn, hSncard⟩ := hS n (by omega)
    have hSnbi : ((Gs n).induce (S n)).IsBipartite := by
      apply bipartite_induce_of_no_short_odd_loops (Gs n) (stageLoopBound n)
        (hodd n (by omega)) (S n) hSn
      dsimp [stageLoopBound]
      omega
    obtain ⟨cout, hcout⟩ := sparse_three_coloring_of_edge_agreement
      (Gs n) (Gs (n+1)) (S n) (hagree n (by omega)) hfinal hSnbi
    have hcoutfin : {v | cout v = 2}.Finite := hSn.subset hcout
    have hcoutcard : {v | cout v = 2}.ncard ≤ 2*(n+1) :=
      (Set.ncard_le_ncard hcout hSn).trans hSncard
    obtain ⟨i, hi⟩ := exists_empty_four_layer height {v | cout v = 2}
      hcoutfin (2*(n+1)) (stageRadius n) hcoutcard
    let t := stageRadius n + 4*i.val + 1
    have ht : t+3 ≤ R := by have := i.isLt; dsimp [t]; omega
    have htpos : 1 ≤ t := by dsimp [t]; omega
    let cin' : V → Fin 3 := fun v => if hv : v ∈ B then cin ⟨v,hv⟩ else 0
    obtain ⟨c, hc⟩ := glue_three_colorings (Gs 0) height t cin' cout hlayer
      (by
        intro v w hvw hv hw
        have hvB : v ∈ B := hv.trans (by omega)
        have hwB : w ∈ B := hw.trans (by omega)
        simpa only [cin', dif_pos hvB, dif_pos hwB] using
          cin.valid (show ((Gs 0).induce B).Adj ⟨v,hvB⟩ ⟨w,hwB⟩ from hvw))
      (by
        intro v w hvw hv hw
        apply cout.valid
        rcases hdiff hvw with h | h
        · exact h
        · have hz := hzero v h.1; omega)
      (by
        intro v hv hw he
        have hvB : v ∈ B := hw.trans (by omega)
        have hhe : cin ⟨v,hvB⟩ = 2 := by simpa only [cin', dif_pos hvB] using he
        have hh := hcinheight ⟨v,hvB⟩ hhe
        change height v ≤ stageRadius n at hh
        dsimp [t] at hv
        omega)
      (by
        intro v hv hw he
        exact hi v he ⟨hv, by dsimp [t] at hw ⊢; omega⟩)
    refine ⟨c, ?_⟩
    intro v hv
    rcases hc v hv with h | h
    · obtain ⟨a, ha, p, hp, _⟩ := hwalk v (h.trans (by omega))
      exact ⟨a, Or.inl ha, p, hp.le.trans (h.trans (by omega))⟩
    · exact ⟨v, Or.inr (hcout h), .nil, by simp⟩


def budgetThreshold (i : ℕ) : ℕ :=
  2*hittingWitnessBound (stageLoopBound i) (i+1)+i

noncomputable def slowBudget (n : ℕ) : ℕ :=
  Nat.find (show ∃ i, n ≤ budgetThreshold i from ⟨n, by dsimp [budgetThreshold]; omega⟩)

lemma slowBudget_spec (n : ℕ) : n ≤ budgetThreshold (slowBudget n) := by
  unfold slowBudget
  exact Nat.find_spec (show ∃ i, n ≤ budgetThreshold i from
    ⟨n, by dsimp [budgetThreshold]; omega⟩)

lemma slowBudget_le (i n : ℕ)
    (hn : n ≤ 2*hittingWitnessBound (stageLoopBound i) (i+1)) : slowBudget n ≤ i := by
  unfold slowBudget
  apply Nat.find_min'
  dsimp [budgetThreshold]
  omega

lemma slowBudget_tendsto : Tendsto slowBudget atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨(∑ i ∈ Finset.range b, budgetThreshold i)+1, ?_⟩
  intro n hn
  by_contra h
  have hmem : slowBudget n ∈ Finset.range b := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum (f := budgetThreshold) (fun i _ => Nat.zero_le _) hmem
  have hs := slowBudget_spec n
  omega

lemma bipartite_of_no_short_odd_loops [Fintype V] (G : SimpleGraph V) (L : ℕ)
    (h : NoShortOddLoops G L) (hcard : 2*Fintype.card V+1 ≤ L) : G.IsBipartite := by
  have hh := bipartite_induce_of_no_short_odd_loops G L h Set.univ Set.finite_univ
    (by simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using hcard)
  exact hh.of_hom { toFun := fun v => ⟨v, Set.mem_univ v⟩, map_rel' := fun h => h }

set_option maxHeartbeats 4000000 in
/-- The explicit divergent budget forces every finite graph to be three-colorable. -/
lemma finite_three_colorable_of_slow_budget [Fintype V] (G : SimpleGraph V)
    (hprofile : ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ slowBudget n) : G.Colorable 3 := by
  classical
  have hdel : ∀ i : ℕ, ∀ H : {H : SimpleGraph V // H ≤ G},
      ∃ E : Finset (Sym2 V), E.card ≤ i ∧
        NoShortOddLoops (H.val.deleteEdges (E : Set (Sym2 V))) (stageLoopBound i) := by
    intro i H
    let φ : H.val →g G := { toFun := id, map_rel' := fun h => H.property h }
    have hHprofile := profile_bound_of_injective_hom φ Function.injective_id slowBudget hprofile
    obtain ⟨E, hE, hodd⟩ := delete_short_odd_loops_of_profile_bound H.val
      (stageLoopBound i) (i+1) (by
        intro n hn
        exact (hHprofile n).trans_lt (Nat.lt_succ_of_le (slowBudget_le i n hn)))
    exact ⟨E, Nat.le_of_lt_succ hE, hodd⟩
  choose Es hEcard hEodd using hdel
  have hzero : NoShortOddLoops G (stageLoopBound 0) := by
    have he : Es 0 ⟨G, le_rfl⟩ = ∅ := Finset.card_eq_zero.mp
      (Nat.eq_zero_of_le_zero (hEcard 0 ⟨G, le_rfl⟩))
    simpa only [he, Finset.coe_empty, SimpleGraph.deleteEdges_empty] using hEodd 0 ⟨G, le_rfl⟩
  let next : ℕ → {H : SimpleGraph V // H ≤ G} → {H : SimpleGraph V // H ≤ G} :=
    fun i H => ⟨H.val.deleteEdges (Es (i+1) H : Set (Sym2 V)),
      (SimpleGraph.deleteEdges_le _).trans H.property⟩
  let seq : ℕ → {H : SimpleGraph V // H ≤ G} := Nat.rec ⟨G, le_rfl⟩ next
  let Gs : ℕ → SimpleGraph V := fun i => (seq i).val
  have heq : ∀ i, Gs (i+1) = (Gs i).deleteEdges (Es (i+1) (seq i) : Set (Sym2 V)) :=
    fun _ => rfl
  have hodd : ∀ i, NoShortOddLoops (Gs i) (stageLoopBound i) := by
    intro i
    cases i with
    | zero => exact hzero
    | succ i => rw [heq]; exact hEodd (i+1) (seq i)
  have hends : ∀ i : ℕ, ∃ S : Set V, S.Finite ∧ S.ncard ≤ 2*(i+1) ∧
      ∀ u v, s(u,v) ∈ Es (i+1) (seq i) → u ∈ S ∧ v ∈ S := by
    intro i
    obtain ⟨S, hS, hc, he⟩ := finite_edge_endpoints
      (Es (i+1) (seq i) : Set (Sym2 V)) (Es (i+1) (seq i)).finite_toSet
    refine ⟨S, hS, hc.trans ?_, he⟩
    simpa only [Set.ncard_coe_finset] using Nat.mul_le_mul_left 2 (hEcard (i+1) (seq i))
  choose S hSfin hScard hSend using hends
  have hagree : ∀ i, ∀ ⦃u v⦄, (Gs i).Adj u v →
      (Gs (i+1)).Adj u v ∨ (u ∈ S i ∧ v ∈ S i) := by
    intro i u v huv
    by_cases he : s(u,v) ∈ Es (i+1) (seq i)
    · exact Or.inr (hSend i u v he)
    · left
      rw [heq]
      exact SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
  let N := 2*Fintype.card V+1
  have hfinal : (Gs N).IsBipartite := by
    apply bipartite_of_no_short_odd_loops (Gs N) (stageLoopBound N) (hodd N)
    dsimp [stageLoopBound, N]
    omega
  obtain ⟨c, _⟩ := multiscale_sparse_coloring N Gs S
    (fun i _ => ⟨hSfin i, hScard i⟩) (fun i _ => hagree i) (fun i _ => hodd i) hfinal
  exact ⟨c⟩


/-- The divergent budget `slowBudget` forces three-colorability of every finite subgraph,
contradicting the finite witnesses required by infinite chromatic number. -/
theorem erdos_74.disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n)) := by
  intro h
  obtain ⟨n, G, hχ, hprofile⟩ :=
    finite_witness_property_of_conjecture h slowBudget slowBudget_tendsto 3
  exact hχ (finite_three_colorable_of_slow_budget G hprofile)

end Erdos74
