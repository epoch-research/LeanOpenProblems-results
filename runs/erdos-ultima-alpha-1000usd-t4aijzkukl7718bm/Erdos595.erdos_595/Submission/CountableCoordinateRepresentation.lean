import Submission.CompleteFilterProduct

/-!
Every nonempty graph embeds in a reduced product of countable induced
subgraphs over a proper countably complete filter. This uses a fine filter,
NOT a countably complete ultrafilter. Consequently the finite-colourability
hypothesis in `CompleteFilterProduct` cannot simply be replaced by
countability of the coordinate vertex sets without addressing the original
non-coverability problem.
-/

set_option autoImplicit false
open Set SimpleGraph Filter
namespace Erdos595CountableCoordinate

variable {V : Type*}

abbrev Index (V : Type*) := {s : Set V // s.Countable}

instance : Nonempty (Index V) := ⟨⟨∅, Set.countable_empty⟩⟩

instance : IsDirectedOrder (Index V) := by
  constructor
  intro s t
  exact ⟨⟨s.1 ∪ t.1, s.2.union t.2⟩, Set.subset_union_left, Set.subset_union_right⟩

/-- The filter of tails of the countable-subset poset. -/
def fine (V : Type*) : Filter (Index V) := Filter.atTop

instance : (fine V).NeBot := Filter.atTop_neBot

/-- Countably many countable lower bounds have a countable upper bound. -/
instance : CountableInterFilter (fine V) where
  countable_sInter_mem := by
    classical
    intro S hS hmem
    letI : Countable S := hS.to_subtype
    have hb : ∀ U : S, ∃ s : Index V, ∀ t ≥ s, t ∈ U.1 := by
      intro U
      exact Filter.mem_atTop_sets.mp (hmem U.1 U.2)
    choose b hb using hb
    let s : Set V := ⋃ U : S, (b U).1
    have hs : s.Countable := Set.countable_iUnion fun U => (b U).2
    apply Filter.mem_atTop_sets.mpr
    refine ⟨⟨s, hs⟩, ?_⟩
    intro t ht
    apply Set.mem_sInter.mpr
    intro U hU
    apply hb ⟨U, hU⟩ t
    exact (Set.subset_iUnion (fun U : S => (b U).1) ⟨U, hU⟩).trans ht

/-- Each prescribed countable set is included eventually. -/
theorem eventually_contains (s : Set V) (hs : s.Countable) :
    ∀ᶠ t in fine V, s ⊆ t.1 :=
  Filter.eventually_atTop.mpr ⟨⟨s, hs⟩, fun _ ht => ht⟩

/-- Adjoin a fixed default vertex so every coordinate type is nonempty. -/
def Carrier (v₀ : V) (s : Index V) := {x : V // x ∈ s.1 ∪ {v₀}}

instance (v₀ : V) (s : Index V) : Countable (Carrier v₀ s) :=
  (s.2.union (Set.countable_singleton v₀)).to_subtype

instance (v₀ : V) (s : Index V) : Nonempty (Carrier v₀ s) :=
  ⟨⟨v₀, Or.inr rfl⟩⟩

noncomputable def project (v₀ x : V) (s : Index V) : Carrier v₀ s := by
  classical
  exact if h : x ∈ s.1 then ⟨x, Or.inl h⟩ else ⟨v₀, Or.inr rfl⟩

@[simp] theorem project_of_mem (v₀ x : V) (s : Index V) (hx : x ∈ s.1) :
    (project v₀ x s).1 = x := by
  classical
  simp [project, hx]

def coordinate (G : SimpleGraph V) (v₀ : V) (s : Index V) :
    SimpleGraph (Carrier v₀ s) := G.comap Subtype.val

def product (G : SimpleGraph V) (v₀ : V) :
    SimpleGraph (∀ s : Index V, Carrier v₀ s) :=
  Erdos595CompleteFilterProduct.graph (fine V) (coordinate G v₀)

/-- The original adjacency relation is recovered exactly, not merely in one
direction. -/
theorem project_adj_iff (G : SimpleGraph V) (v₀ x y : V) :
    (product G v₀).Adj (project v₀ x) (project v₀ y) ↔ G.Adj x y := by
  classical
  have hcontains : ∀ᶠ s in fine V, x ∈ s.1 ∧ y ∈ s.1 := by
    apply (eventually_contains ({x, y} : Set V) (by simp)).mono
    intro s hs
    exact ⟨hs (by simp), hs (by simp)⟩
  constructor
  · intro h
    obtain ⟨s, hs, hxy⟩ := (hcontains.and h).exists
    change G.Adj (project v₀ x s).1 (project v₀ y s).1 at hxy
    simpa only [project_of_mem v₀ x s hs.1, project_of_mem v₀ y s hs.2] using hxy
  · intro h
    apply hcontains.mono
    intro s hs
    change G.Adj (project v₀ x s).1 (project v₀ y s).1
    simpa only [project_of_mem v₀ x s hs.1, project_of_mem v₀ y s hs.2] using h

/-- A graph embedding into the countably complete reduced product. -/
noncomputable def embedding (G : SimpleGraph V) (v₀ : V) : G ↪g product G v₀ where
  toFun := project v₀
  inj' := by
    intro x y h
    let s : Index V := ⟨{x, y}, by simp⟩
    have hv := congrArg Subtype.val (congrFun h s)
    simpa only [project_of_mem v₀ x s (by simp [s]),
      project_of_mem v₀ y s (by simp [s])] using hv
  map_rel_iff' := fun {x y} => project_adj_iff G v₀ x y

/-- All finite clique exclusions pass to any proper-filter reduced product. -/
theorem product_cliqueFree {I : Type*} {A : I → Type*}
    (F : Filter I) [F.NeBot] (G : ∀ i, SimpleGraph (A i)) (n : ℕ)
    (hG : ∀ i, (G i).CliqueFree n) :
    (Erdos595CompleteFilterProduct.graph F G).CliqueFree n := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ a b : Fin n, ∀ᶠ i in F,
      a ≠ b → (G i).Adj (e a i) (e b i) := by
    intro a b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ h => (h hab).elim
    · exact (e.map_rel_iff.mpr hab).mono fun _ hi _ => hi
  have hall : ∀ᶠ i in F, ∀ a b : Fin n, a ≠ b → (G i).Adj (e a i) (e b i) :=
    Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (he a)
  obtain ⟨i, hi⟩ := hall.exists
  let f : (⊤ : SimpleGraph (Fin n)) ↪g G i :=
    { toFun := fun a => e a i
      inj' := fun a b hab => by
        by_contra hne
        exact (hi a b hne).ne hab
      map_rel_iff' := by
        intro a b
        exact ⟨fun h => fun hab => (h.ne (congrArg (fun a => e a i) hab)), hi a b⟩ }
  exact SimpleGraph.not_cliqueFree_of_top_embedding f (hG i)

/-- Each coordinate is an induced subgraph of the original graph. -/
theorem coordinate_cliqueFree (G : SimpleGraph V) (v₀ : V) {n : ℕ}
    (hG : G.CliqueFree n) (s : Index V) : (coordinate G v₀ s).CliqueFree n :=
  hG.comap (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G)

/-- In particular, this representation preserves the `K₄` exclusion. -/
theorem representation_cliqueFree (G : SimpleGraph V) (v₀ : V) {n : ℕ}
    (hG : G.CliqueFree n) : (product G v₀).CliqueFree n :=
  product_cliqueFree (fine V) (coordinate G v₀) n (coordinate_cliqueFree G v₀ hG)

/-- A hypothetical witness remains a witness in the above product family. -/
theorem no_cover_preserved (G : SimpleGraph V) (v₀ : V)
    (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree (product G v₀) :=
  fun h => hG (Erdos595Work.countable_union_of_hom (embedding G v₀).toHom h)

#print axioms project_adj_iff
#print axioms embedding
#print axioms product_cliqueFree
#print axioms representation_cliqueFree
#print axioms no_cover_preserved
end Erdos595CountableCoordinate
