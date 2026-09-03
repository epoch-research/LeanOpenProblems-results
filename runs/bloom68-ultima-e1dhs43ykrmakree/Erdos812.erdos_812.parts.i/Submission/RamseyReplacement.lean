import FormalConjecturesUtil
import Submission.RamseyPrelim

/-!
# The finite two-vertex replacement constraint

Red edges are the edges of a simple graph, and blue edges are its complement.
`HasCap G k` means that neither colour has a clique of size `k + 1`.
An `Allowable G k X` profile joins a new vertex in red to exactly `X`.

The new vertices in `Option (Option U)` are `some none` and `none`; the old
vertices are `some (some u)`.  Unlike edge-maximality, an order bound on *all*
cap-`k` graphs rules out both choices of the edge between these new vertices.
This forces the two blocking cliques in `blocking_cliques_of_no_extension`.
For an old finite set in a larger ambient type, use its subtype as `U`.

The final section connects this constraint to `hypergraphRamsey 2 (k + 1)`
and constructs a critical graph and an allowable profile at the required order.
-/

namespace Combinatorics.RamseyReplacement

variable {U : Type*}

/-- All red and blue cliques have size at most `k`. -/
def HasCap (G : SimpleGraph U) (k : ℕ) : Prop :=
  G.CliqueFree (k + 1) ∧ Gᶜ.CliqueFree (k + 1)

/-- A red-neighbourhood profile is allowable when it has no red `k`-clique,
and its complement has no blue `k`-clique. -/
def Allowable (G : SimpleGraph U) (k : ℕ) (X : Set U) : Prop :=
  G.CliqueFreeOn X k ∧ Gᶜ.CliqueFreeOn Xᶜ k

/-- Add a vertex `none`, with red neighbourhood `X` among the old vertices. -/
def extend (G : SimpleGraph U) (X : Set U) : SimpleGraph (Option U) where
  Adj
    | none, none => False
    | none, some u => u ∈ X
    | some u, none => u ∈ X
    | some u, some v => G.Adj u v
  symm := by
    intro u v h
    cases u <;> cases v
    · exact h
    · exact h
    · exact h
    · exact G.symm h
  loopless := by
    intro u
    cases u
    · exact not_false
    · exact G.loopless _

@[simp] lemma extend_adj_some (G : SimpleGraph U) (X : Set U) (u v : U) :
    (extend G X).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma extend_adj_none_some (G : SimpleGraph U) (X : Set U) (u : U) :
    (extend G X).Adj none (some u) ↔ u ∈ X := Iff.rfl

@[simp] lemma extend_adj_some_none (G : SimpleGraph U) (X : Set U) (u : U) :
    (extend G X).Adj (some u) none ↔ u ∈ X := Iff.rfl

@[simp] lemma extend_compl (G : SimpleGraph U) (X : Set U) :
    (extend G X)ᶜ = extend Gᶜ Xᶜ := by
  ext u v
  cases u <;> cases v <;> simp [extend, SimpleGraph.compl_adj]

/-- Exact clique decomposition, with no lower bound on the clique's size. -/
lemma isClique_extend_iff (G : SimpleGraph U) (X : Set U)
    (s : Finset (Option U)) :
    (extend G X).IsClique s ↔
      G.IsClique s.eraseNone ∧ (none ∈ s → (s.eraseNone : Set U) ⊆ X) := by
  constructor
  · intro hs
    constructor
    · intro u hu v hv huv
      exact hs (Finset.mem_eraseNone.mp hu) (Finset.mem_eraseNone.mp hv)
        (by simpa using huv)
    · intro hn u hu
      exact hs hn (Finset.mem_eraseNone.mp hu) (by simp)
  · rintro ⟨hs, hX⟩ u hu v hv huv
    cases u with
    | none =>
      cases v with
      | none => exact (huv rfl).elim
      | some v => exact hX hu (Finset.mem_eraseNone.mpr hv)
    | some u =>
      cases v with
      | none => exact hX hv (Finset.mem_eraseNone.mpr hu)
      | some v =>
        exact hs (Finset.mem_eraseNone.mpr hu) (Finset.mem_eraseNone.mpr hv)
          (by simpa using huv)

/-- The cardinality budget for adjoining one vertex, on an arbitrary allowed
set of vertices `W`.  A clique uses either zero or one new vertex. -/
lemma cliqueFreeOn_extend {G : SimpleGraph U} {X : Set U}
    {W : Set (Option U)} {n : ℕ}
    (hOld : G.CliqueFreeOn (some ⁻¹' W) (n + 1))
    (hNew : none ∈ W → G.CliqueFreeOn (X ∩ (some ⁻¹' W)) n) :
    (extend G X).CliqueFreeOn W (n + 1) := by
  intro s hsW hs
  obtain ⟨hclique, hprofile⟩ := (isClique_extend_iff G X s).mp hs.isClique
  have hsub : (s.eraseNone : Set U) ⊆ some ⁻¹' W := by
    intro u hu
    exact hsW (Finset.mem_eraseNone.mp hu)
  by_cases hn : none ∈ s
  · apply hNew (hsW hn) (fun u hu => ⟨hprofile hn hu, hsub hu⟩)
    exact ⟨hclique, by simp [Finset.card_eraseNone_of_mem hn, hs.card_eq]⟩
  · apply hOld hsub
    exact ⟨hclique, by rw [Finset.card_eraseNone_of_not_mem hn, hs.card_eq]⟩

/-- A new vertex is allowed exactly when its neighbourhood contains no clique
one smaller than the forbidden clique. -/
lemma cliqueFree_extend_iff (G : SimpleGraph U) (X : Set U) (n : ℕ) :
    (extend G X).CliqueFree (n + 1) ↔
      G.CliqueFree (n + 1) ∧ G.CliqueFreeOn X n := by
  constructor
  · intro h
    constructor
    · intro s hs
      apply h (s.map Function.Embedding.some)
      refine ⟨(isClique_extend_iff G X _).mpr ?_, ?_⟩
      · simpa using hs.isClique
      · simpa using hs.card_eq
    · intro s hsX hs
      apply h s.insertNone
      refine ⟨(isClique_extend_iff G X _).mpr ?_, ?_⟩
      · simpa using And.intro hs.isClique hsX
      · simp only [Finset.card_insertNone, hs.card_eq]
  · rintro ⟨hG, hX⟩
    rw [← SimpleGraph.cliqueFreeOn_univ]
    apply cliqueFreeOn_extend
    · simpa using hG
    · intro _
      simpa using hX

/-- This proves, rather than assumes, that `Allowable` is exactly the condition
for adjoining a single vertex to a cap-`k` graph. -/
lemma hasCap_extend_iff (G : SimpleGraph U) (X : Set U) (k : ℕ) :
    HasCap (extend G X) k ↔ HasCap G k ∧ Allowable G k X := by
  simp only [HasCap, Allowable, extend_compl, cliqueFree_extend_iff]
  tauto

/-- Cardinality formulation of clique-freeness, including empty and singleton
cliques.  This justifies the clique-number interpretation of the hypotheses. -/
lemma cliqueFreeOn_iff_card_lt (G : SimpleGraph U) (X : Set U) (n : ℕ) :
    G.CliqueFreeOn X n ↔
      ∀ s : Finset U, (s : Set U) ⊆ X → G.IsClique s → s.card < n := by
  constructor
  · intro h s hsX hs
    by_contra hn
    obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
    exact h (fun u hu => hsX (hts hu)) ⟨hs.subset hts, ht⟩
  · intro h s hsX hs
    exact (Nat.ne_of_lt (h s hsX hs.isClique)) hs.card_eq

/-- `HasCap` bounds every clique, with no restriction on its arity. -/
lemma hasCap_iff_card_le (G : SimpleGraph U) (k : ℕ) :
    HasCap G k ↔
      (∀ s : Finset U, G.IsClique s → s.card ≤ k) ∧
      (∀ s : Finset U, Gᶜ.IsClique s → s.card ≤ k) := by
  simp only [HasCap, ← SimpleGraph.cliqueFreeOn_univ, cliqueFreeOn_iff_card_lt,
    Set.subset_univ, true_implies, Nat.lt_succ_iff]

/-- The profile hypothesis in the requested clique-number/cardinality form. -/
lemma allowable_iff_card_le (G : SimpleGraph U) (X : Set U) {k : ℕ} (hk : 0 < k) :
    Allowable G k X ↔
      (∀ s : Finset U, (s : Set U) ⊆ X → G.IsClique s → s.card ≤ k - 1) ∧
      (∀ s : Finset U, (s : Set U) ⊆ Xᶜ → Gᶜ.IsClique s → s.card ≤ k - 1) := by
  have hlt : ∀ a : ℕ, a < k ↔ a ≤ k - 1 := by intro a; omega
  simp only [Allowable, cliqueFreeOn_iff_card_lt, hlt]

/-- The second profile includes the first new vertex exactly when `b = true`. -/
def liftProfile (Y : Set U) (b : Bool) : Set (Option U)
  | none => b = true
  | some u => u ∈ Y

@[simp] lemma preimage_liftProfile (Y : Set U) (b : Bool) :
    some ⁻¹' liftProfile Y b = Y := rfl

@[simp] lemma none_mem_liftProfile (Y : Set U) (b : Bool) :
    none ∈ liftProfile Y b ↔ b = true := Iff.rfl

@[simp] lemma some_mem_liftProfile (Y : Set U) (b : Bool) (u : U) :
    some u ∈ liftProfile Y b ↔ u ∈ Y := Iff.rfl

@[simp] lemma liftProfile_compl (Y : Set U) (b : Bool) :
    (liftProfile Y b)ᶜ = liftProfile Yᶜ (!b) := by
  ext u
  cases u <;> cases b <;> simp

/-- Add both replacement vertices; `b = true` means that they are red-joined. -/
def twoVertexExtension (G : SimpleGraph U) (X Y : Set U) (b : Bool) :
    SimpleGraph (Option (Option U)) :=
  extend (extend G X) (liftProfile Y b)

@[simp] lemma twoVertexExtension_compl (G : SimpleGraph U) (X Y : Set U) (b : Bool) :
    (twoVertexExtension G X Y b)ᶜ = twoVertexExtension Gᶜ Xᶜ Yᶜ (!b) := by
  simp [twoVertexExtension]

lemma HasCap.compl {G : SimpleGraph U} {k : ℕ} (h : HasCap G k) : HasCap Gᶜ k := by
  simpa [HasCap, and_comm] using h

lemma Allowable.compl {G : SimpleGraph U} {k : ℕ} {X : Set U}
    (h : Allowable G k X) : Allowable Gᶜ k Xᶜ := by
  simpa [Allowable, and_comm] using h

/-- The essential construction: if the common red neighbourhood has no
`(k - 1)`-clique, red-join the new vertices.  All cliques in the resulting
graph still have size at most `k`, in both colours. -/
lemma hasCap_red_extension {G : SimpleGraph U} {X Y : Set U} {k : ℕ}
    (hk : 2 ≤ k) (hG : HasCap G k) (hX : Allowable G k X)
    (hY : Allowable G k Y) (hXY : G.CliqueFreeOn (X ∩ Y) (k - 1)) :
    HasCap (twoVertexExtension G X Y true) k := by
  have hsucc : k - 1 + 1 = k := by omega
  apply (hasCap_extend_iff _ _ _).mpr
  refine ⟨(hasCap_extend_iff _ _ _).mpr ⟨hG, hX⟩, ?_⟩
  constructor
  · rw [← hsucc]
    apply cliqueFreeOn_extend
    · simpa [hsucc] using hY.1
    · intro _
      simpa using hXY
  · rw [extend_compl, liftProfile_compl, ← hsucc]
    apply cliqueFreeOn_extend
    · simpa [hsucc] using hY.2
    · simp

/-- The colour-dual construction, when the common blue neighbourhood has no
`(k - 1)`-clique. -/
lemma hasCap_blue_extension {G : SimpleGraph U} {X Y : Set U} {k : ℕ}
    (hk : 2 ≤ k) (hG : HasCap G k) (hX : Allowable G k X)
    (hY : Allowable G k Y) (hXY : Gᶜ.CliqueFreeOn (Xᶜ ∩ Yᶜ) (k - 1)) :
    HasCap (twoVertexExtension G X Y false) k := by
  have h := (hasCap_red_extension hk hG.compl hX.compl hY.compl hXY).compl
  simpa using h

/-- **Finite exchange constraint.** If neither choice of the new edge admits a
cap-`k` extension with these two allowable profiles, both blocking cliques
exist.  This does not assume that the old graph is merely edge-maximal.

The conclusion gives actual finite sets of exactly `k - 1` vertices, not just
nonempty neighbourhood intersections.  Finiteness of the ambient type is not
needed for this stronger local formulation. -/
theorem blocking_cliques_of_no_extension {G : SimpleGraph U} {X Y : Set U} {k : ℕ}
    (hk : 2 ≤ k) (hG : HasCap G k) (hX : Allowable G k X)
    (hY : Allowable G k Y)
    (hNo : ∀ b : Bool, ¬ HasCap (twoVertexExtension G X Y b) k) :
    (∃ s : Finset U, (s : Set U) ⊆ X ∩ Y ∧ G.IsNClique (k - 1) s) ∧
    (∃ t : Finset U, (t : Set U) ⊆ (X ∪ Y)ᶜ ∧ Gᶜ.IsNClique (k - 1) t) := by
  classical
  constructor
  · by_contra h
    apply hNo true
    apply hasCap_red_extension hk hG hX hY
    intro s hs hclique
    exact h ⟨s, hs, hclique⟩
  · by_contra h
    apply hNo false
    apply hasCap_blue_extension hk hG hX hY
    intro t ht hclique
    apply h ⟨t, ?_, hclique⟩
    simpa only [Set.compl_union] using ht

/-- The requested genuine global-maximum version.  It suffices to assume the
order bound only for graphs on `Option (Option U)`: that type has `|U| + 2`
vertices, contradicting the bound `|U| + 1` for either constructed extension. -/
theorem blocking_cliques_of_global_order_bound [Fintype U]
    {G : SimpleGraph U} {X Y : Set U} {k : ℕ}
    (hk : 2 ≤ k) (hG : HasCap G k) (hX : Allowable G k X)
    (hY : Allowable G k Y)
    (hMax : ∀ H : SimpleGraph (Option (Option U)), HasCap H k →
      Fintype.card (Option (Option U)) ≤ Fintype.card U + 1) :
    (∃ s : Finset U, (s : Set U) ⊆ X ∩ Y ∧ G.IsNClique (k - 1) s) ∧
    (∃ t : Finset U, (t : Set U) ⊆ (X ∪ Y)ᶜ ∧ Gᶜ.IsNClique (k - 1) t) := by
  apply blocking_cliques_of_no_extension hk hG hX hY
  intro b hb
  have := hMax (twoVertexExtension G X Y b) hb
  simp only [Fintype.card_option] at this
  omega

/-- The blocking cliques occupy disjoint parts of the old vertex set, so their
combined cardinality is charged to `|U|`, not to an enlarged vertex set. -/
theorem replacement_card_budget [Fintype U]
    {G : SimpleGraph U} {X Y : Set U} {k : ℕ}
    (hk : 2 ≤ k) (hG : HasCap G k) (hX : Allowable G k X)
    (hY : Allowable G k Y)
    (hNo : ∀ b : Bool, ¬ HasCap (twoVertexExtension G X Y b) k) :
    2 * (k - 1) ≤ Fintype.card U := by
  classical
  obtain ⟨⟨s, hs, hsc⟩, ⟨t, ht, htc⟩⟩ :=
    blocking_cliques_of_no_extension hk hG hX hY hNo
  have hd : Disjoint s t := Finset.disjoint_left.mpr fun u hus hut =>
    ht hut (Or.inl (hs hus).1)
  have hcard := Finset.card_le_univ (s ∪ t)
  rw [Finset.card_union_of_disjoint hd, hsc.card_eq, htc.card_eq] at hcard
  omega

/- ## Connection with the actual diagonal Ramsey number -/

/-- Interpret a colouring of finite subsets as a simple graph of the edges
of colour `b`.  Only the values on two-element subsets are used. -/
noncomputable def colorGraph (c : Finset U → Bool) (b : Bool) : SimpleGraph U := by
  classical
  exact
    { Adj := fun u v => u ≠ v ∧ c {u, v} = b
      symm := by
        intro u v h
        exact ⟨h.1.symm, by simpa only [Finset.pair_comm] using h.2⟩
      loopless := by
        intro u h
        exact h.1 rfl }

@[simp] lemma colorGraph_compl (c : Finset U → Bool) (b : Bool) :
    (colorGraph c b)ᶜ = colorGraph c (!b) := by
  classical
  ext u v
  simp only [SimpleGraph.compl_adj, colorGraph]
  cases b <;> cases c {u, v} <;> simp

/-- The graph interpretation agrees with the exact subset-colouring
predicate used to define `hypergraphRamsey`, for cliques of every arity. -/
lemma isClique_colorGraph_iff (c : Finset U → Bool) (b : Bool) (s : Finset U) :
    (colorGraph c b).IsClique s ↔
      ∀ e : Finset U, e ⊆ s → e.card = 2 → c e = b := by
  classical
  constructor
  · intro hs e hes hecard
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hecard
    exact (hs (hes (by simp)) (hes (by simp)) huv).2
  · intro hs u hu v hv huv
    refine ⟨huv, hs {u, v} ?_ (Finset.card_pair huv)⟩
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hu hv

/-- Encode a graph as a Boolean colouring; on pairs, `true` means adjacency. -/
noncomputable def graphColoring (G : SimpleGraph U) : Finset U → Bool := by
  classical
  exact fun e => decide (G.IsClique e)

@[simp] lemma colorGraph_graphColoring (G : SimpleGraph U) :
    colorGraph (graphColoring G) true = G := by
  classical
  ext u v
  by_cases huv : u = v
  · simp [huv]
  · simp [colorGraph, graphColoring, huv]

/-- The defining Ramsey predicate is exactly nonexistence of a cap-`k` graph
of that order, not an edge-maximality condition. -/
lemma hasRamseyProperty_iff_no_cap (m k : ℕ) :
    RamseyPrelim.HasRamseyProperty m (k + 1) ↔
      ∀ G : SimpleGraph (Fin m), ¬ HasCap G k := by
  classical
  constructor
  · intro h G hG
    obtain ⟨s, hs, b, hmono⟩ := h (graphColoring G)
    have hclique := (isClique_colorGraph_iff (graphColoring G) b s).mpr hmono
    cases b
    · have hblue : Gᶜ.IsClique s := by
        rw [← colorGraph_graphColoring G, colorGraph_compl]
        exact hclique
      exact hG.2 s ⟨hblue, hs⟩
    · have hred : G.IsClique s := by simpa using hclique
      exact hG.1 s ⟨hred, hs⟩
  · intro h c
    have hex : ∃ b : Bool, ∃ s : Finset (Fin m),
        (colorGraph c b).IsNClique (k + 1) s := by
      by_contra hn
      push_neg at hn
      apply h (colorGraph c true)
      exact ⟨hn true, by simpa using hn false⟩
    obtain ⟨b, s, hs⟩ := hex
    exact ⟨s, hs.card_eq, b, (isClique_colorGraph_iff c b s).mp hs.isClique⟩

/-- Below the Ramsey number the defining universal property fails, so an
actual critical Boolean colouring exists on `R(k + 1) - 1` vertices. -/
theorem exists_critical_coloring (k : ℕ) :
    ∃ c : Finset (Fin (hypergraphRamsey 2 (k + 1) - 1)) → Bool,
      ¬ ∃ s : Finset (Fin (hypergraphRamsey 2 (k + 1) - 1)),
        s.card = k + 1 ∧ ∃ b : Bool,
          ∀ e : Finset (Fin (hypergraphRamsey 2 (k + 1) - 1)),
            e ⊆ s → e.card = 2 → c e = b := by
  classical
  have hn : ¬ RamseyPrelim.HasRamseyProperty
      (hypergraphRamsey 2 (k + 1) - 1) (k + 1) := by
    intro h
    have hle := RamseyPrelim.ramsey_le_of_property h
    have hpos := RamseyPrelim.ramsey_pos (Nat.succ_pos k)
    exact (Nat.sub_lt hpos Nat.one_pos).not_ge hle
  simpa only [RamseyPrelim.HasRamseyProperty, not_forall] using hn

/-- A critical graph really exists on `N = R(k + 1) - 1` vertices. -/
theorem exists_critical_graph (k : ℕ) :
    ∃ G : SimpleGraph (Fin (hypergraphRamsey 2 (k + 1) - 1)), HasCap G k := by
  obtain ⟨c, hc⟩ := exists_critical_coloring k
  refine ⟨colorGraph c true, ?_, ?_⟩
  · intro s hs
    exact hc ⟨s, hs.card_eq, true,
      (isClique_colorGraph_iff c true s).mp hs.isClique⟩
  · rw [colorGraph_compl]
    intro s hs
    exact hc ⟨s, hs.card_eq, false,
      (isClique_colorGraph_iff c false s).mp hs.isClique⟩

/-- Restriction along an injection preserves both clique bounds. -/
lemma HasCap.comap {V : Type*} {G : SimpleGraph U} {k : ℕ}
    (h : HasCap G k) (f : V ↪ U) : HasCap (G.comap f) k := by
  constructor
  · exact h.1.comap (SimpleGraph.Embedding.comap f G)
  · have heq : (G.comap f)ᶜ = Gᶜ.comap f := by
      ext u v
      simp [SimpleGraph.compl_adj, f.injective.eq_iff]
    rw [heq]
    exact h.2.comap (SimpleGraph.Embedding.comap f Gᶜ)

/-- **Genuine global order bound.** Every finite cap-`k` graph has at most
`R(k + 1) - 1` vertices. -/
theorem card_le_ramsey_sub_one [Fintype U] {G : SimpleGraph U} {k : ℕ}
    (hG : HasCap G k) : Fintype.card U ≤ hypergraphRamsey 2 (k + 1) - 1 := by
  by_contra h
  have hle : Fintype.card (Fin (hypergraphRamsey 2 (k + 1))) ≤ Fintype.card U := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  have hNo := (hasRamseyProperty_iff_no_cap (hypergraphRamsey 2 (k + 1)) k).mp
    (RamseyPrelim.ramsey_property (k + 1))
  exact hNo (G.comap f) (hG.comap f)

/-- On `R(k + 1) - 2` old vertices the replacement constraint follows from the
actual Ramsey number, with no maximality hypothesis left to assume. -/
theorem blocking_cliques_at_ramsey [Fintype U]
    {G : SimpleGraph U} {X Y : Set U} {k : ℕ}
    (hk : 2 ≤ k) (hcard : Fintype.card U + 1 = hypergraphRamsey 2 (k + 1) - 1)
    (hG : HasCap G k) (hX : Allowable G k X) (hY : Allowable G k Y) :
    (∃ s : Finset U, (s : Set U) ⊆ X ∩ Y ∧ G.IsNClique (k - 1) s) ∧
    (∃ t : Finset U, (t : Set U) ⊆ (X ∪ Y)ᶜ ∧ Gᶜ.IsNClique (k - 1) t) := by
  apply blocking_cliques_of_global_order_bound hk hG hX hY
  intro H hH
  rw [hcard]
  exact card_le_ramsey_sub_one hH

/-- Any graph with a distinguished vertex is obtained by the one-vertex
extension construction from its old graph and the distinguished profile. -/
lemma extend_comap_some (H : SimpleGraph (Option U)) :
    extend (H.comap some) {u | H.Adj none (some u)} = H := by
  ext u v
  cases u <;> cases v <;> simp [extend, SimpleGraph.adj_comm]

/-- Deleting a vertex from a critical graph supplies an old graph and an
allowable profile on `R(k + 1) - 2` vertices.  Thus the setting of
`blocking_cliques_at_ramsey` is inhabited, not just a conditional abstraction. -/
theorem exists_critical_profile {k : ℕ} (hk : 2 ≤ k) :
    ∃ G : SimpleGraph (Fin (hypergraphRamsey 2 (k + 1) - 2)),
      ∃ X : Set (Fin (hypergraphRamsey 2 (k + 1) - 2)),
        HasCap G k ∧ Allowable G k X := by
  obtain ⟨G, hG⟩ := exists_critical_graph k
  have hR := RamseyPrelim.le_ramsey (k + 1)
  have hle : Fintype.card (Option (Fin (hypergraphRamsey 2 (k + 1) - 2))) ≤
      Fintype.card (Fin (hypergraphRamsey 2 (k + 1) - 1)) := by
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  let H := G.comap f
  have hH : HasCap H k := hG.comap f
  refine ⟨H.comap some, {u | H.Adj none (some u)}, ?_⟩
  apply (hasCap_extend_iff _ _ _).mp
  rwa [extend_comap_some]

end Combinatorics.RamseyReplacement

#print axioms Combinatorics.RamseyReplacement.hasCap_extend_iff
#print axioms Combinatorics.RamseyReplacement.cliqueFreeOn_iff_card_lt
#print axioms Combinatorics.RamseyReplacement.hasCap_red_extension
#print axioms Combinatorics.RamseyReplacement.hasCap_blue_extension
#print axioms Combinatorics.RamseyReplacement.blocking_cliques_of_no_extension
#print axioms Combinatorics.RamseyReplacement.blocking_cliques_of_global_order_bound

#print axioms Combinatorics.RamseyReplacement.hasRamseyProperty_iff_no_cap
#print axioms Combinatorics.RamseyReplacement.exists_critical_coloring
#print axioms Combinatorics.RamseyReplacement.exists_critical_graph
#print axioms Combinatorics.RamseyReplacement.card_le_ramsey_sub_one
#print axioms Combinatorics.RamseyReplacement.blocking_cliques_at_ramsey
#print axioms Combinatorics.RamseyReplacement.exists_critical_profile

#print axioms Combinatorics.RamseyReplacement.hasCap_iff_card_le
#print axioms Combinatorics.RamseyReplacement.allowable_iff_card_le
#print axioms Combinatorics.RamseyReplacement.replacement_card_budget
