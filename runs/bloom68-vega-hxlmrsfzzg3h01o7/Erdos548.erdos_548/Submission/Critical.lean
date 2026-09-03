import FormalConjecturesUtil

/-!
# Finite-tree embeddings and positive-excess critical graphs

This file is independent of `Submission.Spec` and `Submission.Auxiliary`.  It proves
infrastructure, not the Erdős–Sós conjecture.

* A finite tree on `m + 1` vertices has an ordinary `SimpleGraph.Copy` in a nonempty
  finite host of minimum degree at least `m`.  The copy need not be induced.
* Every finite positive-excess graph has a nonempty induced `IsInducedCritical`
  subgraph.  Each nonempty vertex set in it is incident to more than the threshold
  number of edges; consequently its minimum degree is at least `ceil(k / 2)` and
  its maximum degree is at least `k`.
* Positive excess is measured over `ℚ`, with coefficient `((k : ℚ) - 1) / 2`;
  in particular there is no truncated subtraction at `k = 0`.

The nonempty-host hypothesis matters for the one-vertex tree: mathlib assigns
minimum degree zero to the graph with no vertices.  The incident-edge inequality
likewise requires a nonempty vertex set: for the empty set both sides are zero.
-/

open SimpleGraph

namespace Erdos548.Critical

universe u v

section TreeEmbedding

/-- If at least `|A|` neighbors are available at an already used vertex, one of
those neighbors is outside the image of `A`.  The used vertex itself is not its
own neighbor.  The function `f` need not be injective. -/
theorem exists_adj_not_mem_range {A : Type u} {V : Type v}
    [Fintype A] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : A → V) (a : A) (hdeg : Fintype.card A ≤ G.degree (f a)) :
    ∃ w, G.Adj (f a) w ∧ ∀ x, f x ≠ w := by
  classical
  by_contra! h
  have hsub : G.neighborFinset (f a) ⊆ Finset.univ.image f := by
    intro w hw
    obtain ⟨x, hx⟩ := h w ((G.mem_neighborFinset _ _).mp hw)
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  have hstrict : G.neighborFinset (f a) ⊂ Finset.univ.image f := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    have hm : f a ∈ G.neighborFinset (f a) :=
      heq.symm ▸ Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    exact G.loopless _ ((G.mem_neighborFinset _ _).mp hm)
  have hlt := Finset.card_lt_card hstrict
  have hle : (Finset.univ.image f).card ≤ Fintype.card A :=
    (Finset.card_image_le).trans_eq (Finset.card_univ)
  rw [G.card_neighborFinset_eq_degree] at hlt
  omega

/-- A graph on at most one vertex has an ordinary copy in every nonempty host. -/
theorem isContained_of_subsingleton {A : Type u} {V : Type v}
    [Subsingleton A] [Nonempty V] (T : SimpleGraph A) (G : SimpleGraph V) :
    T.IsContained G := by
  obtain ⟨w⟩ := ‹Nonempty V›
  refine ⟨{
    toHom := { toFun := fun _ => w, map_rel' := ?_ }
    injective' := fun _ _ _ => Subsingleton.elim _ _ }⟩
  intro x y hxy
  exact (hxy.ne (Subsingleton.elim x y)).elim

/-- Greedy leaf induction, in a form convenient for changing the tree's vertex
subtype.  Only adjacency preservation is asserted: this is ordinary containment,
not induced containment. -/
theorem isContained_of_isTree_of_card_le_degree_add_one
    {A : Type u} {V : Type v} [Fintype A] [Fintype V] [Nonempty V]
    (T : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (hG : ∀ w, Fintype.card A ≤ G.degree w + 1) :
    T.IsContained G := by
  classical
  suffices main : ∀ n : ℕ, ∀ {B : Type u} [Fintype B], Fintype.card B = n →
      ∀ (R : SimpleGraph B), R.IsTree →
        (∀ w, n ≤ G.degree w + 1) → R.IsContained G by
    exact main _ rfl T hT hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ hn R hR hdegree
    by_cases hsmall : Fintype.card B ≤ 1
    · letI : Subsingleton B := Fintype.card_le_one_iff_subsingleton.mp hsmall
      exact isContained_of_subsingleton R G
    · letI : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨leaf, hleaf⟩ := hR.exists_vert_degree_one_of_nontrivial
      let s : Set B := {leaf}ᶜ
      have hs_card : Fintype.card s = n - 1 := by
        dsimp [s]
        rw [Fintype.card_compl_set]
        simp [hn]
      have hs_lt : Fintype.card s < n := by omega
      have hs_tree : (R.induce s).IsTree :=
        ⟨hR.isConnected.induce_compl_singleton_of_degree_eq_one hleaf,
          hR.IsAcyclic.induce s⟩
      obtain ⟨f⟩ := ih (Fintype.card s) hs_lt rfl (R.induce s) hs_tree
        (fun w => by have := hdegree w; omega)
      obtain ⟨parent, hadj, hparent⟩ :=
        SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hleaf
      have hp : parent ≠ leaf := hadj.ne.symm
      let p : s := ⟨parent, hp⟩
      obtain ⟨w, hw, hfresh⟩ := exists_adj_not_mem_range G (fun x => f x) p
        (by change Fintype.card s ≤ G.degree (f p); have := hdegree (f p); omega)
      let g : B → V := fun x => if hx : x = leaf then w else f ⟨x, hx⟩
      refine ⟨{ toHom := { toFun := g, map_rel' := ?_ }, injective' := ?_ }⟩
      · intro x y hxy
        by_cases hx : x = leaf
        · subst x
          have hy : y = parent := hparent y hxy
          subst y
          simpa [g, p, hp] using hw.symm
        · by_cases hy : y = leaf
          · subst y
            have hx' : x = parent := hparent x hxy.symm
            subst x
            simpa [g, p, hp] using hw
          · exact (show G.Adj (g x) (g y) from by
              simpa only [g, dif_neg hx, dif_neg hy] using
                f.toHom.map_rel (show (R.induce s).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))
      · intro x y hxy
        change g x = g y at hxy
        by_cases hx : x = leaf
        · by_cases hy : y = leaf
          · exact hx.trans hy.symm
          · have heq : w = f ⟨y, hy⟩ := by simpa [g, hx, hy] using hxy
            exact (hfresh ⟨y, hy⟩ heq.symm).elim
        · by_cases hy : y = leaf
          · have heq : f ⟨x, hx⟩ = w := by simpa [g, hx, hy] using hxy
            exact (hfresh ⟨x, hx⟩ heq).elim
          · have heq : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
              simpa only [g, dif_neg hx, dif_neg hy] using hxy
            exact congrArg Subtype.val (f.injective heq)

/-- Every finite tree embeds as an ordinary copy in a nonempty finite graph
whose minimum degree is at least the number of tree vertices minus one. -/
theorem isContained_of_isTree_of_minDegree
    {A : Type u} {V : Type v} [Fintype A] [Fintype V] [Nonempty V]
    (T : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (hG : Fintype.card A - 1 ≤ G.minDegree) :
    T.IsContained G := by
  apply isContained_of_isTree_of_card_le_degree_add_one T G hT
  intro w
  have := G.minDegree_le_degree w
  omega

/-- The usual `m + 1`-vertex formulation of the greedy tree embedding theorem. -/
theorem isContained_of_isTree_of_card_eq_succ_of_minDegree
    {A : Type u} {V : Type v} [Fintype A] [Fintype V] [Nonempty V]
    (T : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hcard : Fintype.card A = m + 1) (hT : T.IsTree)
    (hG : m ≤ G.minDegree) : T.IsContained G := by
  apply isContained_of_isTree_of_minDegree T G hT
  simpa [hcard] using hG

/-- A `Finite`-only variant: degrees are neighbor-set `ncard`s, so the statement
requires neither enumerations nor decidable adjacency instances. -/
theorem isContained_of_isTree_of_neighborSet_ncard
    {A : Type u} {V : Type v} [Finite A] [Finite V] [Nonempty V]
    (T : SimpleGraph A) (G : SimpleGraph V) (hT : T.IsTree)
    (hG : ∀ w, Nat.card A ≤ (G.neighborSet w).ncard + 1) : T.IsContained G := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite V
  apply isContained_of_isTree_of_card_le_degree_add_one T G hT
  intro w
  simpa only [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card',
    SimpleGraph.degree, SimpleGraph.neighborFinset] using hG w

/-- The `m + 1`-vertex theorem using only `Finite` vertex types and neighbor-set
cardinalities. -/
theorem isContained_of_isTree_of_card_eq_succ_of_neighborSet_ncard
    {A : Type u} {V : Type v} [Finite A] [Finite V] [Nonempty V]
    (T : SimpleGraph A) (G : SimpleGraph V) (m : ℕ)
    (hcard : Nat.card A = m + 1) (hT : T.IsTree)
    (hG : ∀ w, m ≤ (G.neighborSet w).ncard) : T.IsContained G := by
  apply isContained_of_isTree_of_neighborSet_ncard T G hT
  intro w
  rw [hcard]
  exact Nat.add_le_add_right (hG w) 1

/-- Specialization to `Fin`: the host-size condition supplies nonemptiness,
including for the one-vertex tree. -/
theorem fin_tree_isContained_of_minDegree {n m : ℕ} (hn : m + 1 ≤ n)
    (T : SimpleGraph (Fin (m + 1))) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hT : T.IsTree) (hG : m ≤ G.minDegree) :
    T.IsContained G := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact isContained_of_isTree_of_card_eq_succ_of_minDegree T G m (Fintype.card_fin _)
    hT hG

end TreeEmbedding

section PositiveExcess

variable {V : Type u} {W : Type v}

/-- Excess over the Erdős–Sós half-integral threshold.  All arithmetic, especially
`k - 1`, takes place in `ℚ`, so this definition also treats `k = 0` correctly. -/
noncomputable def excess (k : ℕ) (G : SimpleGraph V) : ℚ :=
  (G.edgeSet.ncard : ℚ) - ((k : ℚ) - 1) / 2 * Nat.card V

/-- Positive excess, minimal under deleting vertices.  Every proper induced
subgraph (including the empty one) is at or below the same threshold. -/
structure IsInducedCritical (k : ℕ) (G : SimpleGraph V) : Prop where
  positive : 0 < excess k G
  proper : ∀ s : Set V, s ≠ Set.univ → excess k (G.induce s) ≤ 0

/-- Edge-set cardinality does not depend on the vertex labels. -/
theorem ncard_edgeSet_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard :=
  Set.ncard_congr' e.mapEdgeSet

/-- Excess is invariant under graph isomorphism. -/
theorem excess_iso (k : ℕ) {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    excess k G = excess k H := by
  unfold excess
  rw [ncard_edgeSet_iso e, Nat.card_congr e.toEquiv]

@[simp]
theorem excess_induce_univ (k : ℕ) (G : SimpleGraph V) :
    excess k (G.induce Set.univ) = excess k G :=
  excess_iso k G.induceUnivIso

@[simp]
theorem excess_of_isEmpty [IsEmpty V] (k : ℕ) (G : SimpleGraph V) :
    excess k G = 0 := by
  have hbot : G = ⊥ := Subsingleton.elim _ _
  simp [excess, hbot]

/-- A positive-excess graph has at least one vertex, even when `k = 0`. -/
theorem nonempty_of_excess_pos (k : ℕ) (G : SimpleGraph V) (h : 0 < excess k G) :
    Nonempty V := by
  by_contra hempty
  haveI : IsEmpty V := not_nonempty_iff.mp hempty
  simp at h

/-- Flatten two successive vertex restrictions, without changing adjacency. -/
noncomputable def induceInduceIso (G : SimpleGraph V) (s : Set V) (t : Set s) :
    (G.induce s).induce t ≃g G.induce (Subtype.val '' t) where
  toEquiv := Equiv.Set.image (Subtype.val : s → V) t Subtype.val_injective
  map_rel_iff' := by intro x y; rfl

/-- Every finite graph of positive excess has a nonempty induced subgraph that
is minimal for positive excess.  This uses minimum vertex cardinality, not any
unproved tree-containment assertion. -/
theorem exists_induced_critical [Finite V] (k : ℕ) (G : SimpleGraph V)
    (hG : 0 < excess k G) :
    ∃ s : Set V, s.Nonempty ∧ IsInducedCritical k (G.induce s) := by
  obtain ⟨s, hs, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun s : Set V => 0 < excess k (G.induce s)) Set.ncard
    ⟨Set.univ, by simpa using hG⟩
  refine ⟨s, Set.nonempty_coe_sort.mp (nonempty_of_excess_pos k _ hs), hs, ?_⟩
  intro t ht
  have hproper : Subtype.val '' t ⊂ s := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
    · intro heq
      apply ht
      apply Set.eq_univ_of_forall
      intro x
      have hx : x.val ∈ Subtype.val '' t := heq.symm ▸ x.property
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := Subtype.val_injective hyx
      simpa [hyx'] using hy
  have hlt := Set.ncard_lt_ncard hproper
  by_contra! hpos
  have himage : 0 < excess k (G.induce (Subtype.val '' t)) := by
    rw [← excess_iso k (induceInduceIso G s t)]
    exact hpos
  exact (not_le_of_gt hlt) (hmin himage hlt.le)

/-- Threshold-form version of `exists_induced_critical`, with no natural-number
subtraction in the coefficient. -/
theorem exists_induced_critical_of_edge_threshold [Finite V]
    (k : ℕ) (G : SimpleGraph V)
    (hG : ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ)) :
    ∃ s : Set V, s.Nonempty ∧ IsInducedCritical k (G.induce s) := by
  apply exists_induced_critical k G
  exact sub_pos.mpr hG

/-- The set of edges incident to at least one vertex of `s`.  An edge with both
endpoints in `s` is counted once, not twice. -/
def incidentEdges (G : SimpleGraph V) (s : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ x ∈ s, x ∈ e}

@[simp]
theorem incidentEdges_empty (G : SimpleGraph V) : incidentEdges G ∅ = ∅ := by
  ext e
  simp [incidentEdges]

@[simp]
theorem incidentEdges_singleton (G : SimpleGraph V) (x : V) :
    incidentEdges G {x} = G.incidenceSet x := by
  ext e
  simp [incidentEdges, SimpleGraph.incidenceSet]

/-- For a singleton, incident-edge cardinality is precisely degree, expressed
without a chosen `Fintype` instance. -/
theorem ncard_incidentEdges_singleton (G : SimpleGraph V) (x : V) :
    (incidentEdges G {x}).ncard = (G.neighborSet x).ncard := by
  classical
  rw [incidentEdges_singleton]
  exact Set.ncard_congr' (G.incidenceSetEquivNeighborSet x)

/-- The image of the induced edge set consists exactly of the host edges whose
two endpoints lie in the inducing vertex set. -/
theorem image_edgeSet_induce (G : SimpleGraph V) (s : Set V) :
    Sym2.map (Subtype.val : s → V) '' (G.induce s).edgeSet = G.edgeSet ∩ s.sym2 := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    constructor
    · rintro ⟨e, he, heq⟩
      induction e using Sym2.ind with
      | h x y =>
        change G.Adj x.val y.val at he
        change s(x.val, y.val) = s(a, b) at heq
        rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨hb, ha⟩
        · exact ⟨ha ▸ hb ▸ he, ha ▸ x.property, hb ▸ y.property⟩
        · exact ⟨ha ▸ hb ▸ he.symm, ha ▸ y.property, hb ▸ x.property⟩
    · rintro ⟨hadj, ha, hb⟩
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hadj, rfl⟩

/-- Induced edge counts can be calculated inside the original edge type. -/
theorem ncard_edgeSet_induce (G : SimpleGraph V) (s : Set V) :
    (G.induce s).edgeSet.ncard = (G.edgeSet ∩ s.sym2).ncard := by
  rw [← image_edgeSet_induce]
  exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm

/-- Removing all edges incident to `s` leaves precisely the edges supported on
its complement. -/
theorem edgeSet_diff_incidentEdges (G : SimpleGraph V) (s : Set V) :
    G.edgeSet \ incidentEdges G s = G.edgeSet ∩ sᶜ.sym2 := by
  ext e
  simp only [Set.mem_diff, incidentEdges, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_sym2_iff_subset, Set.subset_def, Set.mem_compl_iff]
  aesop

/-- Exact edge partition: edges remaining after deleting `s`, plus edges
incident to `s`, are all the edges.  No truncated subtraction is used. -/
theorem ncard_induce_compl_add_incidentEdges [Finite V]
    (G : SimpleGraph V) (s : Set V) :
    (G.induce sᶜ).edgeSet.ncard + (incidentEdges G s).ncard = G.edgeSet.ncard := by
  rw [ncard_edgeSet_induce, ← edgeSet_diff_incidentEdges]
  exact Set.ncard_diff_add_ncard_of_subset (fun _ h => h.1)

/-- A critical graph is nonempty; this is derived from its positive excess. -/
theorem IsInducedCritical.nonempty {k : ℕ} {G : SimpleGraph V}
    (h : IsInducedCritical k G) : Nonempty V :=
  nonempty_of_excess_pos k G h.positive

/-- The positive edge threshold of a critical graph, unpacked from `excess`. -/
theorem IsInducedCritical.edge_threshold {k : ℕ} {G : SimpleGraph V}
    (h : IsInducedCritical k G) :
    ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ) :=
  sub_pos.mp h.positive

/-- Every proper induced subgraph of a critical graph is at or below the edge
threshold, including the empty induced subgraph. -/
theorem IsInducedCritical.proper_edge_threshold {k : ℕ} {G : SimpleGraph V}
    (h : IsInducedCritical k G) {s : Set V} (hs : s ≠ Set.univ) :
    ((G.induce s).edgeSet.ncard : ℚ) ≤ ((k : ℚ) - 1) / 2 * s.ncard := by
  simpa only [excess, Nat.card_coe_set_eq, sub_nonpos] using h.proper s hs

/-- Deleting a nonempty vertex set from a critical graph loses strictly more
than `((k : ℚ) - 1) / 2` edges per deleted vertex.  The nonempty hypothesis is
necessary: for `s = ∅`, both sides would be zero. -/
theorem IsInducedCritical.incidentEdges_bound [Finite V] {k : ℕ} {G : SimpleGraph V}
    (h : IsInducedCritical k G) {s : Set V} (hs : s.Nonempty) :
    ((k : ℚ) - 1) / 2 * s.ncard < ((incidentEdges G s).ncard : ℚ) := by
  have hpos := h.positive
  have hdel := h.proper sᶜ (Set.compl_ne_univ.mpr hs)
  have he : ((G.induce sᶜ).edgeSet.ncard : ℚ) + (incidentEdges G s).ncard =
      (G.edgeSet.ncard : ℚ) := by
    exact_mod_cast ncard_induce_compl_add_incidentEdges G s
  have hv : (s.ncard : ℚ) + sᶜ.ncard = (Nat.card V : ℚ) := by
    exact_mod_cast Set.ncard_add_ncard_compl s
  simp only [excess, Nat.card_coe_set_eq] at hpos hdel
  rw [← hv] at hpos
  nlinarith

/-- The singleton case of the incident-edge bound, with degree as a set
cardinality.  This statement only requires `Finite V`. -/
theorem IsInducedCritical.neighborSet_bound [Finite V] {k : ℕ} {G : SimpleGraph V}
    (h : IsInducedCritical k G) (x : V) :
    ((k : ℚ) - 1) / 2 < ((G.neighborSet x).ncard : ℚ) := by
  simpa only [Set.ncard_singleton, Nat.cast_one, mul_one, ncard_incidentEdges_singleton]
    using h.incidentEdges_bound (Set.singleton_nonempty x)

/-- Integrality upgrades the strict rational degree bound to `k ≤ 2 deg(x)`.
The intermediate integer subtraction is not truncated when `k = 0`. -/
theorem IsInducedCritical.two_mul_neighborSet_ncard_ge [Finite V]
    {k : ℕ} {G : SimpleGraph V} (h : IsInducedCritical k G) (x : V) :
    k ≤ 2 * (G.neighborSet x).ncard := by
  have hq : (k : ℚ) - 1 < 2 * ((G.neighborSet x).ncard : ℚ) := by
    have := h.neighborSet_bound x
    linarith
  have hz : (k : ℤ) - 1 < 2 * ((G.neighborSet x).ncard : ℤ) := by
    exact_mod_cast hq
  have hz' : (k : ℤ) ≤ 2 * ((G.neighborSet x).ncard : ℤ) := by omega
  exact_mod_cast hz'

/-- Every vertex of a critical graph has degree at least `ceil(k / 2)`.
Here `⌈·⌉₊` is the natural-valued ceiling. -/
theorem IsInducedCritical.neighborSet_ncard_ge_ceil [Finite V]
    {k : ℕ} {G : SimpleGraph V} (h : IsInducedCritical k G) (x : V) :
    ⌈(k : ℚ) / 2⌉₊ ≤ (G.neighborSet x).ncard := by
  apply Nat.ceil_le.mpr
  have hq : (k : ℚ) ≤ 2 * ((G.neighborSet x).ncard : ℚ) := by
    exact_mod_cast h.two_mul_neighborSet_ncard_ge x
  linarith

/-- Convert enumeration-independent degree to mathlib's degree. -/
theorem ncard_neighborSet_eq_degree (G : SimpleGraph V) (x : V)
    [Fintype (G.neighborSet x)] : (G.neighborSet x).ncard = G.degree x :=
  (Set.ncard_eq_toFinset_card' _).trans (G.card_neighborFinset_eq_degree x)

/-- A subtraction-free integer form of the critical minimum-degree bound. -/
theorem IsInducedCritical.two_mul_minDegree_ge [Fintype V]
    {k : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj] (h : IsInducedCritical k G) :
    k ≤ 2 * G.minDegree := by
  letI : Nonempty V := h.nonempty
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  rw [hx, ← ncard_neighborSet_eq_degree]
  exact h.two_mul_neighborSet_ncard_ge x

/-- Minimum degree at least `ceil(k / 2)`, stated with mathlib's `minDegree`. -/
theorem IsInducedCritical.minDegree_ge_ceil [Fintype V]
    {k : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj] (h : IsInducedCritical k G) :
    ⌈(k : ℚ) / 2⌉₊ ≤ G.minDegree := by
  apply Nat.ceil_le.mpr
  have hq : (k : ℚ) ≤ 2 * (G.minDegree : ℚ) := by
    exact_mod_cast h.two_mul_minDegree_ge
  linarith

/-- Equivalent division-on-naturals form of the critical minimum-degree bound. -/
theorem IsInducedCritical.minDegree_ge_half [Fintype V]
    {k : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj] (h : IsInducedCritical k G) :
    (k + 1) / 2 ≤ G.minDegree := by
  have := h.two_mul_minDegree_ge
  omega

/-- The degree-sum formula implies that any finite positive-excess graph has a
vertex of degree at least `k`.  Criticality is not needed for this conclusion. -/
theorem exists_degree_ge_of_excess_pos [Fintype V] (k : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : 0 < excess k G) : ∃ x, k ≤ G.degree x := by
  classical
  by_contra! hsmall
  have hsum : ∑ x : V, (G.degree x + 1) ≤ ∑ _x : V, k :=
    Finset.sum_le_sum fun x _ => Nat.succ_le_iff.mpr (hsmall x)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, G.sum_degrees_eq_twice_card_edges] at hsum
  have hq : 2 * (G.edgeSet.ncard : ℚ) + (Nat.card V : ℚ) ≤ (Nat.card V : ℚ) * k := by
    simp only [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card']
    exact_mod_cast hsum
  unfold excess at h
  nlinarith

/-- The maximum-degree consequence of positive excess. -/
theorem maxDegree_ge_of_excess_pos [Fintype V] (k : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : 0 < excess k G) : k ≤ G.maxDegree := by
  obtain ⟨x, hx⟩ := exists_degree_ge_of_excess_pos k G h
  exact hx.trans (G.degree_le_maxDegree x)

/-- Enumeration-independent form of the maximum-degree consequence. -/
theorem exists_neighborSet_ncard_ge_of_excess_pos [Finite V]
    (k : ℕ) (G : SimpleGraph V) (h : 0 < excess k G) :
    ∃ x, k ≤ (G.neighborSet x).ncard := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := exists_degree_ge_of_excess_pos k G h
  exact ⟨x, by simpa only [ncard_neighborSet_eq_degree] using hx⟩

/-- In particular, a critical graph has maximum degree at least `k`. -/
theorem IsInducedCritical.maxDegree_ge [Fintype V]
    {k : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj] (h : IsInducedCritical k G) :
    k ≤ G.maxDegree :=
  maxDegree_ge_of_excess_pos k G h.positive

/-- The positive-excess reduction, packaged without choosing enumerations of
vertex subtypes.  The last two clauses express `δ(H) ≥ ceil(k / 2)` and
`Δ(H) ≥ k`; the preceding clause is the incident-edge inequality for every
nonempty vertex set of `H = G.induce s`. -/
theorem exists_critical_reduction [Finite V] (k : ℕ) (G : SimpleGraph V)
    (hG : ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ)) :
    ∃ s : Set V, s.Nonempty ∧ IsInducedCritical k (G.induce s) ∧
      (∀ t : Set s, t.Nonempty →
        ((k : ℚ) - 1) / 2 * t.ncard < ((incidentEdges (G.induce s) t).ncard : ℚ)) ∧
      (∀ x : s, ⌈(k : ℚ) / 2⌉₊ ≤ ((G.induce s).neighborSet x).ncard) ∧
      (∃ x : s, k ≤ ((G.induce s).neighborSet x).ncard) := by
  obtain ⟨s, hs, hc⟩ := exists_induced_critical_of_edge_threshold k G hG
  exact ⟨s, hs, hc, fun _ ht => hc.incidentEdges_bound ht,
    hc.neighborSet_ncard_ge_ceil,
    exists_neighborSet_ncard_ge_of_excess_pos k (G.induce s) hc.positive⟩

end PositiveExcess

end Erdos548.Critical

/- Transitive axiom audit for every theorem in this file. -/
#print axioms Erdos548.Critical.exists_adj_not_mem_range
#print axioms Erdos548.Critical.isContained_of_subsingleton
#print axioms Erdos548.Critical.isContained_of_isTree_of_card_le_degree_add_one
#print axioms Erdos548.Critical.isContained_of_isTree_of_minDegree
#print axioms Erdos548.Critical.isContained_of_isTree_of_card_eq_succ_of_minDegree
#print axioms Erdos548.Critical.isContained_of_isTree_of_neighborSet_ncard
#print axioms Erdos548.Critical.isContained_of_isTree_of_card_eq_succ_of_neighborSet_ncard
#print axioms Erdos548.Critical.fin_tree_isContained_of_minDegree
#print axioms Erdos548.Critical.ncard_edgeSet_iso
#print axioms Erdos548.Critical.excess_iso
#print axioms Erdos548.Critical.excess_induce_univ
#print axioms Erdos548.Critical.excess_of_isEmpty
#print axioms Erdos548.Critical.nonempty_of_excess_pos
#print axioms Erdos548.Critical.exists_induced_critical
#print axioms Erdos548.Critical.exists_induced_critical_of_edge_threshold
#print axioms Erdos548.Critical.incidentEdges_empty
#print axioms Erdos548.Critical.incidentEdges_singleton
#print axioms Erdos548.Critical.ncard_incidentEdges_singleton
#print axioms Erdos548.Critical.image_edgeSet_induce
#print axioms Erdos548.Critical.ncard_edgeSet_induce
#print axioms Erdos548.Critical.edgeSet_diff_incidentEdges
#print axioms Erdos548.Critical.ncard_induce_compl_add_incidentEdges
#print axioms Erdos548.Critical.IsInducedCritical.nonempty
#print axioms Erdos548.Critical.IsInducedCritical.edge_threshold
#print axioms Erdos548.Critical.IsInducedCritical.proper_edge_threshold
#print axioms Erdos548.Critical.IsInducedCritical.incidentEdges_bound
#print axioms Erdos548.Critical.IsInducedCritical.neighborSet_bound
#print axioms Erdos548.Critical.IsInducedCritical.two_mul_neighborSet_ncard_ge
#print axioms Erdos548.Critical.IsInducedCritical.neighborSet_ncard_ge_ceil
#print axioms Erdos548.Critical.ncard_neighborSet_eq_degree
#print axioms Erdos548.Critical.IsInducedCritical.two_mul_minDegree_ge
#print axioms Erdos548.Critical.IsInducedCritical.minDegree_ge_ceil
#print axioms Erdos548.Critical.IsInducedCritical.minDegree_ge_half
#print axioms Erdos548.Critical.exists_degree_ge_of_excess_pos
#print axioms Erdos548.Critical.maxDegree_ge_of_excess_pos
#print axioms Erdos548.Critical.exists_neighborSet_ncard_ge_of_excess_pos
#print axioms Erdos548.Critical.IsInducedCritical.maxDegree_ge
#print axioms Erdos548.Critical.exists_critical_reduction
