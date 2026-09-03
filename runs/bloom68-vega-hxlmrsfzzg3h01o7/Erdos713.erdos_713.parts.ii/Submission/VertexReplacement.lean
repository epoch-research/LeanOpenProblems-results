import FormalConjecturesUtil

/-!
# Exact vertex-neighborhood replacement constraints

Replacing the neighborhood of one vertex leaves the induced graph on the other
vertices unchanged. Its edge count is the edge count of that induced graph plus
the size of the new neighborhood. An ordinary copy of `H` either avoids the
replaced vertex, or comes from a copy of `H - x` whose images of the neighbors of
`x` all lie in the new neighborhood.

These are exact, finite optimization statements, not asymptotic estimates or a
proof of rationality of an extremal exponent. Isolated vertices and the empty
forbidden graph are allowed; in particular, freeness of the vertex-deleted host
must not be dropped from the unconditional copy criterion.

Only the counting and extremal statements require a finite host. The forbidden
vertex type need not be finite, and no bipartiteness or degree assumptions are
used. Decidability instances in the finite API may be supplied by `classical`.
-/

open SimpleGraph

namespace Erdos713VertexReplacement

universe u w

variable {V : Type u} {W : Type w}

/-- Replace the edges incident to `v` by edges from `v` to `S`, preserving every
other edge. If `v ∈ S`, it is silently discarded, so the result is always a
simple graph. The exact neighborhood and counting statements assume `v ∉ S`. -/
def replaceNeighborhood (G : SimpleGraph W) (v : W) (S : Set W) : SimpleGraph W where
  Adj a b := (a = v ∧ b ≠ v ∧ b ∈ S) ∨ (b = v ∧ a ≠ v ∧ a ∈ S) ∨
    (a ≠ v ∧ b ≠ v ∧ G.Adj a b)
  symm := by
    intro a b hab
    rcases hab with h | h | ⟨ha, hb, hab⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hb, ha, hab.symm⟩)
  loopless := by
    intro a haa
    rcases haa with ⟨ha, hne, _⟩ | ⟨ha, hne, _⟩ | ⟨_, _, haa⟩
    · exact hne ha
    · exact hne ha
    · exact G.loopless a haa

variable {H : SimpleGraph V} {G : SimpleGraph W} {v a b : W} {S : Set W}

instance instDecidableRelReplaceNeighborhood [DecidableEq W] [DecidableRel G.Adj]
    [DecidablePred (· ∈ S)] : DecidableRel (replaceNeighborhood G v S).Adj := by
  intro a b
  change Decidable ((a = v ∧ b ≠ v ∧ b ∈ S) ∨ (b = v ∧ a ≠ v ∧ a ∈ S) ∨
    (a ≠ v ∧ b ≠ v ∧ G.Adj a b))
  infer_instance

@[simp]
lemma replaceNeighborhood_adj_left :
    (replaceNeighborhood G v S).Adj v a ↔ a ≠ v ∧ a ∈ S := by
  simp [replaceNeighborhood]

@[simp]
lemma replaceNeighborhood_adj_right :
    (replaceNeighborhood G v S).Adj a v ↔ a ≠ v ∧ a ∈ S := by
  simp [replaceNeighborhood]

/-- Adjacency away from the replaced vertex is unchanged. -/
lemma replaceNeighborhood_adj_of_ne (ha : a ≠ v) (hb : b ≠ v) :
    (replaceNeighborhood G v S).Adj a b ↔ G.Adj a b := by
  simp [replaceNeighborhood, ha, hb]

/-- When `v ∉ S`, the new neighbors of `v` are exactly `S`. -/
lemma neighborSet_replaceNeighborhood (hS : v ∉ S) :
    (replaceNeighborhood G v S).neighborSet v = S := by
  ext a
  simp only [mem_neighborSet, replaceNeighborhood_adj_left]
  exact and_iff_right_of_imp (fun ha hav => hS (hav ▸ ha))

/-- The induced graph after deleting `v` is unaffected by replacement. -/
@[simp]
lemma induce_replaceNeighborhood (G : SimpleGraph W) (v : W) (S : Set W) :
    (replaceNeighborhood G v S).induce ({v}ᶜ : Set W) = G.induce ({v}ᶜ : Set W) := by
  ext a b
  exact replaceNeighborhood_adj_of_ne
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using a.2)
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.2)

/-- Replacing by the original neighborhood recovers the original graph. -/
@[simp]
lemma replaceNeighborhood_neighborSet (G : SimpleGraph W) (v : W) :
    replaceNeighborhood G v (G.neighborSet v) = G := by
  ext a b
  by_cases ha : a = v
  · subst a
    simp only [replaceNeighborhood_adj_left, mem_neighborSet]
    exact and_iff_right_of_imp (fun hab => hab.ne.symm)
  · by_cases hb : b = v
    · subst b
      simp only [replaceNeighborhood_adj_right, mem_neighborSet]
      exact ⟨fun h => h.2.symm, fun hab => ⟨ha, hab.symm⟩⟩
    · exact replaceNeighborhood_adj_of_ne ha hb

/-- Extend a copy of `H - x` in `G - v` by sending `x` to `v`. This uses only
edge preservation, not induced embeddings, and includes isolated `x`. -/
lemma isContained_replaceNeighborhood_of_copy (x : V)
    (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W)))
    (hφ : ∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S) :
    H ⊑ replaceNeighborhood G v S := by
  classical
  have hne : ∀ y, (φ y).1 ≠ v := fun y => by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (φ y).2
  let f : V → W := fun a => if ha : a = x then v else (φ ⟨a, by simpa using ha⟩).1
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro a b hab
    by_cases ha : a = x
    · subst a
      have hb : b ≠ x := hab.ne.symm
      have hnew : (replaceNeighborhood G v S).Adj v (φ ⟨b, by simpa using hb⟩).1 :=
        replaceNeighborhood_adj_left.mpr ⟨hne _, hφ _ hab⟩
      simpa [f, hb] using hnew
    · by_cases hb : b = x
      · subst b
        have hnew : (replaceNeighborhood G v S).Adj (φ ⟨a, by simpa using ha⟩).1 v :=
          replaceNeighborhood_adj_right.mpr ⟨hne _, hφ _ hab.symm⟩
        simpa [f, ha] using hnew
      · have hmap : G.Adj (φ ⟨a, by simpa using ha⟩).1 (φ ⟨b, by simpa using hb⟩).1 :=
          φ.toHom.map_adj hab
        have hnew := (replaceNeighborhood_adj_of_ne (S := S) (hne _) (hne _)).mpr hmap
        simpa [f, ha, hb] using hnew
  · intro a b hab
    by_cases ha : a = x
    · by_cases hb : b = x
      · exact ha.trans hb.symm
      · have heq : v = (φ ⟨b, by simpa using hb⟩).1 := by simpa [f, ha, hb] using hab
        exact (hne _ heq.symm).elim
    · by_cases hb : b = x
      · have heq : (φ ⟨a, by simpa using ha⟩).1 = v := by simpa [f, ha, hb] using hab
        exact (hne _ heq).elim
      · have heq : (φ ⟨a, by simpa using ha⟩).1 = (φ ⟨b, by simpa using hb⟩).1 := by
          simpa [f, ha, hb] using hab
        exact congrArg Subtype.val (φ.injective (Subtype.ext heq))

/-- Every ordinary copy either avoids `v`, or uses `v` as the image of some
`x` and restricts to a copy of `H - x` in `G - v`. No finiteness is needed. -/
theorem isContained_replaceNeighborhood_iff :
    H ⊑ replaceNeighborhood G v S ↔
      H ⊑ G.induce ({v}ᶜ : Set W) ∨
        ∃ (x : V) (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W))),
          ∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S := by
  classical
  constructor
  · rintro ⟨f⟩
    by_cases hhit : ∃ x, f x = v
    · obtain ⟨x, hx⟩ := hhit
      right
      have hne : ∀ y : ({x}ᶜ : Set V), f y.1 ≠ v := by
        intro y hy
        have hyx : y.1 = x := f.injective (hy.trans hx.symm)
        exact (show y.1 ≠ x by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2) hyx
      let φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W)) := by
        refine ⟨⟨fun y => ⟨f y.1, by simpa using hne y⟩, ?_⟩, ?_⟩
        · intro a b hab
          exact (replaceNeighborhood_adj_of_ne (hne a) (hne b)).mp (f.toHom.map_adj hab)
        · intro a b hab
          exact Subtype.ext (f.injective (congrArg Subtype.val hab))
      refine ⟨x, φ, ?_⟩
      intro y hxy
      have hmap : (replaceNeighborhood G v S).Adj v (f y.1) := by
        simpa only [Copy.toHom_apply, hx] using f.toHom.map_adj hxy
      exact (replaceNeighborhood_adj_left.mp hmap).2
    · left
      have hne : ∀ x, f x ≠ v := by simpa only [not_exists] using hhit
      refine ⟨⟨⟨fun x => ⟨f x, by simpa using hne x⟩, ?_⟩, ?_⟩⟩
      · intro a b hab
        exact (replaceNeighborhood_adj_of_ne (hne a) (hne b)).mp (f.toHom.map_adj hab)
      · intro a b hab
        exact f.injective (congrArg Subtype.val hab)
  · rintro (h | ⟨x, φ, hφ⟩)
    · have h' : H ⊑ (replaceNeighborhood G v S).induce ({v}ᶜ : Set W) := by
        rwa [induce_replaceNeighborhood]
      exact h'.trans ⟨Copy.induce _ _⟩
    · exact isContained_replaceNeighborhood_of_copy x φ hφ

/-- Unconditional, exact `H`-freeness criterion. The first conjunct is essential
for empty `H`; the universal condition alone would then be vacuous. -/
theorem free_replaceNeighborhood_iff :
    H.Free (replaceNeighborhood G v S) ↔
      H.Free (G.induce ({v}ᶜ : Set W)) ∧
        ∀ (x : V) (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W))),
          ¬ (∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S) := by
  simp only [Free, isContained_replaceNeighborhood_iff, not_or, not_exists]

/-- If `G - v` is `H`-free, replacement is `H`-free exactly when every copy of
every `H - x` has a neighbor of `x` whose image is outside `S`. For isolated `x`,
the universal neighbor condition is true, so any such copy is forbidden. -/
theorem free_replaceNeighborhood_iff_of_induce_free
    (hcore : H.Free (G.induce ({v}ᶜ : Set W))) :
    H.Free (replaceNeighborhood G v S) ↔
      ∀ (x : V) (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W))),
        ¬ (∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S) := by
  rw [free_replaceNeighborhood_iff]
  exact and_iff_right hcore

/-- In particular the copy criterion applies to every `H`-free original host. -/
theorem free_replaceNeighborhood_iff_of_free (hG : H.Free G) :
    H.Free (replaceNeighborhood G v S) ↔
      ∀ (x : V) (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W))),
        ¬ (∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S) := by
  apply free_replaceNeighborhood_iff_of_induce_free
  exact fun h => hG (h.trans ⟨Copy.induce G _⟩)

section Finite

open scoped Classical

variable [Fintype W] [DecidableEq W]

/-- Split the edges into those avoiding `v` and those incident to `v`. -/
lemma card_edgeFinset_eq_induce_add_degree (G : SimpleGraph W) [DecidableRel G.Adj] (v : W) :
    G.edgeFinset.card = (G.induce ({v}ᶜ : Set W)).edgeFinset.card + G.degree v := by
  rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
  exact (Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)).symm

variable [DecidableRel G.Adj] [DecidablePred (· ∈ S)]

/-- The degree of the replaced vertex is exactly the size of `S`. -/
lemma degree_replaceNeighborhood (hS : v ∉ S) :
    (replaceNeighborhood G v S).degree v = S.toFinset.card := by
  have hN : (replaceNeighborhood G v S).neighborFinset v = S.toFinset := by
    apply Finset.coe_injective
    simpa only [coe_neighborFinset, Set.coe_toFinset] using neighborSet_replaceNeighborhood hS
  change ((replaceNeighborhood G v S).neighborFinset v).card = _
  rw [hN]

/-- Exact edge count after replacement: old edges avoiding `v`, plus `|S|`. -/
theorem card_edgeFinset_replaceNeighborhood (hS : v ∉ S) :
    (replaceNeighborhood G v S).edgeFinset.card =
      (G.induce ({v}ᶜ : Set W)).edgeFinset.card + S.toFinset.card := by
  rw [card_edgeFinset_eq_induce_add_degree _ v, degree_replaceNeighborhood hS]
  have he : (replaceNeighborhood G v S).induce ({v}ᶜ : Set W) ≃g
      G.induce ({v}ᶜ : Set W) := by
    rw [induce_replaceNeighborhood]
  exact congrArg (· + S.toFinset.card) he.card_edgeFinset_eq

/-- Equivalent subtraction form of the replacement edge count. -/
theorem card_edgeFinset_replaceNeighborhood_eq_sub_add (hS : v ∉ S) :
    (replaceNeighborhood G v S).edgeFinset.card =
      G.edgeFinset.card - G.degree v + S.toFinset.card := by
  rw [card_edgeFinset_replaceNeighborhood hS, G.card_edgeFinset_induce_compl_singleton,
    G.card_edgeFinset_deleteIncidenceSet]

/-- Any `H`-free replacement in a graph with `extremalNumber` edges has at most
as many new neighbors as old neighbors. This inequality only needs the edge
count equality; freeness of `G` is needed below to attain the bound. -/
theorem card_le_degree_of_free_replaceNeighborhood
    (hmax : G.edgeFinset.card = extremalNumber (Fintype.card W) H)
    (hS : v ∉ S) (hfree : H.Free (replaceNeighborhood G v S)) :
    S.toFinset.card ≤ G.degree v := by
  have hbound := card_edgeFinset_le_extremalNumber hfree
  have hreplace := card_edgeFinset_replaceNeighborhood (G := G) hS
  have hsplit := card_edgeFinset_eq_induce_add_degree G v
  omega

/-- The extremal bound stated directly in terms of all vertex-deleted copies. -/
theorem card_le_degree_of_copy_constraints (hG : H.Free G)
    (hmax : G.edgeFinset.card = extremalNumber (Fintype.card W) H)
    (hS : v ∉ S)
    (hcopies : ∀ (x : V)
      (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W))),
      ¬ (∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S)) :
    S.toFinset.card ≤ G.degree v :=
  card_le_degree_of_free_replaceNeighborhood hmax hS
    ((free_replaceNeighborhood_iff_of_free hG).mpr hcopies)

/-- The original neighborhood attains the exact maximum cardinality among all
sets excluding `v` that give `H`-free replacements. This is a global edge
extremality consequence, not merely a one-edge saturation condition. -/
theorem isGreatest_feasible_card (hG : H.Free G)
    (hmax : G.edgeFinset.card = extremalNumber (Fintype.card W) H) (v : W) :
    IsGreatest
      ((fun S : Set W => S.toFinset.card) ''
        {S : Set W | v ∉ S ∧ H.Free (replaceNeighborhood G v S)})
      (G.degree v) := by
  refine ⟨⟨G.neighborSet v, ⟨by simp, ?_⟩, ?_⟩, ?_⟩
  · simpa only [replaceNeighborhood_neighborSet] using hG
  · change _ = (G.neighborFinset v).card
    apply congrArg Finset.card
    ext a
    simp only [Set.mem_toFinset, mem_neighborFinset, mem_neighborSet]
  · rintro _ ⟨S, ⟨hS, hfree⟩, rfl⟩
    exact card_le_degree_of_free_replaceNeighborhood hmax hS hfree

/-- Exact maximum using only the copy constraints, without naming a hypergraph.
In particular, no assumptions on isolated vertices of `H` are imposed. -/
theorem isGreatest_copy_feasible_card (hG : H.Free G)
    (hmax : G.edgeFinset.card = extremalNumber (Fintype.card W) H) (v : W) :
    IsGreatest
      ((fun S : Set W => S.toFinset.card) ''
        {S : Set W | v ∉ S ∧
          ∀ (x : V) (φ : (H.induce ({x}ᶜ : Set V)).Copy (G.induce ({v}ᶜ : Set W))),
            ¬ (∀ y : ({x}ᶜ : Set V), H.Adj x y.1 → (φ y).1 ∈ S)})
      (G.degree v) := by
  simpa only [free_replaceNeighborhood_iff_of_free hG] using
    isGreatest_feasible_card hG hmax v

/-- The extremal number is the fixed edge count on `G - v` plus the maximum
feasible replacement cardinality, with that maximum attained at `N_G(v)`. -/
theorem extremalNumber_eq_induce_add_maximum (hG : H.Free G)
    (hmax : G.edgeFinset.card = extremalNumber (Fintype.card W) H) (v : W) :
    ∃ m : ℕ,
      IsGreatest
        ((fun S : Set W => S.toFinset.card) ''
          {S : Set W | v ∉ S ∧ H.Free (replaceNeighborhood G v S)}) m ∧
      extremalNumber (Fintype.card W) H =
        (G.induce ({v}ᶜ : Set W)).edgeFinset.card + m :=
  ⟨G.degree v, isGreatest_feasible_card hG hmax v,
    hmax.symm.trans (card_edgeFinset_eq_induce_add_degree G v)⟩

end Finite

end Erdos713VertexReplacement

#print axioms Erdos713VertexReplacement.replaceNeighborhood
#print axioms Erdos713VertexReplacement.instDecidableRelReplaceNeighborhood
#print axioms Erdos713VertexReplacement.replaceNeighborhood_adj_left
#print axioms Erdos713VertexReplacement.replaceNeighborhood_adj_right
#print axioms Erdos713VertexReplacement.replaceNeighborhood_adj_of_ne
#print axioms Erdos713VertexReplacement.neighborSet_replaceNeighborhood
#print axioms Erdos713VertexReplacement.induce_replaceNeighborhood
#print axioms Erdos713VertexReplacement.replaceNeighborhood_neighborSet
#print axioms Erdos713VertexReplacement.isContained_replaceNeighborhood_of_copy
#print axioms Erdos713VertexReplacement.isContained_replaceNeighborhood_iff
#print axioms Erdos713VertexReplacement.free_replaceNeighborhood_iff
#print axioms Erdos713VertexReplacement.free_replaceNeighborhood_iff_of_induce_free
#print axioms Erdos713VertexReplacement.free_replaceNeighborhood_iff_of_free
#print axioms Erdos713VertexReplacement.card_edgeFinset_eq_induce_add_degree
#print axioms Erdos713VertexReplacement.degree_replaceNeighborhood
#print axioms Erdos713VertexReplacement.card_edgeFinset_replaceNeighborhood
#print axioms Erdos713VertexReplacement.card_edgeFinset_replaceNeighborhood_eq_sub_add
#print axioms Erdos713VertexReplacement.card_le_degree_of_free_replaceNeighborhood
#print axioms Erdos713VertexReplacement.card_le_degree_of_copy_constraints
#print axioms Erdos713VertexReplacement.isGreatest_feasible_card
#print axioms Erdos713VertexReplacement.isGreatest_copy_feasible_card
#print axioms Erdos713VertexReplacement.extremalNumber_eq_induce_add_maximum
