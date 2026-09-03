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

namespace E74
open SimpleGraph
universe u v
variable {V : Type u} {W : Type v}

/-- Edges on which a binary assignment agrees. -/
def badGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ c x = c y
  symm := by intro x y h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := by intro x h; exact G.loopless x h.1

@[simp] theorem badGraph_adj (G : SimpleGraph V) (c : V → Bool) (x y : V) :
    (badGraph G c).Adj x y ↔ G.Adj x y ∧ c x = c y := Iff.rfl

/-- Retain the edges with both endpoints in a prescribed finite vertex set. -/
def on (G : SimpleGraph V) (s : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ s ∧ y ∈ s
  symm := by intro x y h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by intro x h; exact G.loopless x h.1

@[simp] theorem on_adj (G : SimpleGraph V) (s : Finset V) (x y : V) :
    (on G s).Adj x y ↔ G.Adj x y ∧ x ∈ s ∧ y ∈ s := Iff.rfl

noncomputable def errors [Fintype V] (G : SimpleGraph V) (c : V → Bool) :
    Finset (Sym2 V) := by
  classical
  exact (badGraph G c).edgeFinset

noncomputable def defect [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf (Set.range fun c : V → Bool => (errors G c).card)

noncomputable def profile [Fintype V] (G : SimpleGraph V) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.powerset.filter fun s : Finset V => s.card ≤ n)).sup
    (fun s => defect (on G s))

end E74

/-
# Finite binary-coloring defect and its local profile

Universal finite graph tools for `E74Defs`. Restrictions keep the original vertex
universe (vertices outside the specified finset are isolated). In particular, none
of the results assumes that the vertex type or the specified vertex sets are
nonempty.
-/

namespace E74
open SimpleGraph
universe u v
variable {V : Type u} {W : Type v}

/- ## Restrictions and monochromatic edges -/

@[simp] theorem on_empty (G : SimpleGraph V) : on G ∅ = ⊥ := by
  ext x y
  simp

@[simp] theorem on_bot (s : Finset V) : on (⊥ : SimpleGraph V) s = ⊥ := by
  ext x y
  simp

@[simp] theorem on_univ [Fintype V] (G : SimpleGraph V) : on G Finset.univ = G := by
  classical
  ext x y
  simp

theorem on_le (G : SimpleGraph V) (s : Finset V) : on G s ≤ G :=
  fun _ _ h => h.1

theorem on_mono {G H : SimpleGraph V} (h : G ≤ H) (s : Finset V) : on G s ≤ on H s :=
  fun _ _ hxy => ⟨h hxy.1, hxy.2⟩

theorem on_mono_set (G : SimpleGraph V) {s t : Finset V} (h : s ⊆ t) :
    on G s ≤ on G t :=
  fun _ _ hxy => ⟨hxy.1, h hxy.2.1, h hxy.2.2⟩

@[simp] theorem on_on [DecidableEq V] (G : SimpleGraph V) (s t : Finset V) :
    on (on G s) t = on G (s ∩ t) := by
  ext x y
  simp only [on_adj, Finset.mem_inter]
  tauto

theorem on_on_of_subset (G : SimpleGraph V) {s t : Finset V} (h : s ⊆ t) :
    on (on G t) s = on G s := by
  classical
  rw [on_on, Finset.inter_eq_right.mpr h]

theorem badGraph_le (G : SimpleGraph V) (c : V → Bool) : badGraph G c ≤ G :=
  fun _ _ h => h.1

theorem badGraph_mono {G H : SimpleGraph V} (h : G ≤ H) (c : V → Bool) :
    badGraph G c ≤ badGraph H c := fun _ _ hxy => ⟨h hxy.1, hxy.2⟩

@[simp] theorem badGraph_bot (c : V → Bool) : badGraph (⊥ : SimpleGraph V) c = ⊥ := by
  ext x y
  simp

theorem badGraph_on (G : SimpleGraph V) (s : Finset V) (c : V → Bool) :
    badGraph (on G s) c = on (badGraph G c) s := by
  ext x y
  simp only [badGraph_adj, on_adj]
  tauto

section Finite
variable [Fintype V]

@[simp] theorem mem_errors (G : SimpleGraph V) (c : V → Bool) (x y : V) :
    s(x, y) ∈ errors G c ↔ G.Adj x y ∧ c x = c y := by
  classical
  simp [errors]

@[simp] theorem mem_errors_on (G : SimpleGraph V) (s : Finset V)
    (c : V → Bool) (x y : V) :
    s(x, y) ∈ errors (on G s) c ↔ G.Adj x y ∧ x ∈ s ∧ y ∈ s ∧ c x = c y := by
  simp only [mem_errors, on_adj]
  tauto

@[simp] theorem mem_on_edgeFinset (G : SimpleGraph V) (s : Finset V) (x y : V) :
    s(x, y) ∈ (on G s).edgeFinset ↔ G.Adj x y ∧ x ∈ s ∧ y ∈ s := by
  classical
  simp

@[simp] theorem errors_bot (c : V → Bool) : errors (⊥ : SimpleGraph V) c = ∅ := by
  classical
  simp [errors]

theorem errors_mono {G H : SimpleGraph V} (h : G ≤ H) (c : V → Bool) :
    errors G c ⊆ errors H c := by
  classical
  exact SimpleGraph.edgeFinset_mono (badGraph_mono h c)

theorem errors_on_subset (G : SimpleGraph V) (s : Finset V) (c : V → Bool) :
    errors (on G s) c ⊆ errors G c := errors_mono (on_le G s) c

theorem errors_on_mono (G : SimpleGraph V) {s t : Finset V} (h : s ⊆ t)
    (c : V → Bool) : errors (on G s) c ⊆ errors (on G t) c :=
  errors_mono (on_mono_set G h) c

theorem errors_on_eq_filter [DecidableEq V] (G : SimpleGraph V) (s : Finset V) (c : V → Bool) :
    errors (on G s) c = (errors G c).filter (fun e => ∀ x ∈ e, x ∈ s) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf x y => simp [and_assoc, and_left_comm, and_comm]

/- ## The minimum defect -/

theorem exists_optimal (G : SimpleGraph V) :
    ∃ c : V → Bool, (errors G c).card = defect G := by
  exact Nat.sInf_mem (Set.range_nonempty (fun c : V → Bool => (errors G c).card))

theorem defect_le_errors (G : SimpleGraph V) (c : V → Bool) :
    defect G ≤ (errors G c).card := Nat.sInf_le ⟨c, rfl⟩

theorem defect_le_iff_cut (G : SimpleGraph V) (b : ℕ) :
    defect G ≤ b ↔ ∃ c : V → Bool, (errors G c).card ≤ b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_optimal G
    exact ⟨c, hc.trans_le h⟩
  · rintro ⟨c, hc⟩
    exact (defect_le_errors G c).trans hc

theorem le_defect_iff (G : SimpleGraph V) (b : ℕ) :
    b ≤ defect G ↔ ∀ c : V → Bool, b ≤ (errors G c).card := by
  constructor
  · intro h c
    exact h.trans (defect_le_errors G c)
  · intro h
    obtain ⟨c, hc⟩ := exists_optimal G
    simpa only [hc] using h c

theorem defect_mono {G H : SimpleGraph V} (h : G ≤ H) : defect G ≤ defect H := by
  obtain ⟨c, hc⟩ := exists_optimal H
  calc
    defect G ≤ (errors G c).card := defect_le_errors G c
    _ ≤ (errors H c).card := Finset.card_le_card (errors_mono h c)
    _ = defect H := hc

theorem defect_on_le (G : SimpleGraph V) (s : Finset V) : defect (on G s) ≤ defect G :=
  defect_mono (on_le G s)

theorem defect_on_mono (G : SimpleGraph V) {s t : Finset V} (h : s ⊆ t) :
    defect (on G s) ≤ defect (on G t) := defect_mono (on_mono_set G h)

@[simp] theorem defect_bot : defect (⊥ : SimpleGraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using defect_le_errors (⊥ : SimpleGraph V) (fun _ => false)

@[simp] theorem defect_on_empty (G : SimpleGraph V) : defect (on G ∅) = 0 := by simp

theorem errors_eq_empty_iff (G : SimpleGraph V) (c : V → Bool) :
    errors G c = ∅ ↔ ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y := by
  constructor
  · intro h x y hxy heq
    have : s(x, y) ∈ errors G c := (mem_errors G c x y).mpr ⟨hxy, heq⟩
    simp [h] at this
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have he' := (mem_errors G c x y).mp he
      exact h he'.1 he'.2

theorem defect_zero_iff (G : SimpleGraph V) :
    defect G = 0 ↔ ∃ c : V → Bool, ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y := by
  rw [← Nat.le_zero, defect_le_iff_cut]
  simp only [Nat.le_zero, Finset.card_eq_zero, errors_eq_empty_iff]

theorem defect_zero_iff_colorable (G : SimpleGraph V) :
    defect G = 0 ↔ G.Colorable 2 := by
  rw [defect_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    simpa using (SimpleGraph.Coloring.mk c (fun hxy => hc hxy)).colorable
  · intro h
    let c : G.Coloring Bool := h.toColoring (by simp)
    exact ⟨c, fun _ _ hxy => c.valid hxy⟩

/- ## The finite local profile -/

theorem defect_on_le_profile (G : SimpleGraph V) {s : Finset V} {n : ℕ}
    (hs : s.card ≤ n) : defect (on G s) ≤ profile G n := by
  classical
  exact Finset.le_sup (f := fun s => defect (on G s)) (by simp [hs])

theorem profile_le_iff (G : SimpleGraph V) (n b : ℕ) :
    profile G n ≤ b ↔ ∀ s : Finset V, s.card ≤ n → defect (on G s) ≤ b := by
  classical
  simp [profile, Finset.sup_le_iff]

theorem profile_monotone (G : SimpleGraph V) : Monotone (profile G) := by
  intro m n hmn
  apply (profile_le_iff G m (profile G n)).mpr
  intro s hs
  exact defect_on_le_profile G (hs.trans hmn)

theorem profile_le_defect (G : SimpleGraph V) (n : ℕ) : profile G n ≤ defect G := by
  apply (profile_le_iff G n (defect G)).mpr
  intro s _
  exact defect_on_le G s

theorem profile_eq_defect (G : SimpleGraph V) {n : ℕ} (hn : Fintype.card V ≤ n) :
    profile G n = defect G := by
  classical
  apply Nat.le_antisymm (profile_le_defect G n)
  simpa using (defect_on_le_profile G (s := Finset.univ) (by simpa using hn))

theorem exists_profile_set (G : SimpleGraph V) (n : ℕ) :
    ∃ s : Finset V, s.card ≤ n ∧ defect (on G s) = profile G n := by
  classical
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup
    (Finset.univ.powerset.filter fun s : Finset V => s.card ≤ n)
    (by exact ⟨∅, by simp⟩) (fun s => defect (on G s))
  exact ⟨s, (Finset.mem_filter.mp hs).2, heq.symm⟩

@[simp] theorem profile_zero (G : SimpleGraph V) : profile G 0 = 0 := by
  obtain ⟨s, hs, heq⟩ := exists_profile_set G 0
  have hs' : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
  simpa [hs'] using heq.symm

@[simp] theorem profile_bot (n : ℕ) : profile (⊥ : SimpleGraph V) n = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using profile_le_defect (⊥ : SimpleGraph V) n)

theorem profile_mono {G H : SimpleGraph V} (h : G ≤ H) (n : ℕ) :
    profile G n ≤ profile H n := by
  apply (profile_le_iff G n (profile H n)).mpr
  intro s hs
  exact (defect_mono (on_mono h s)).trans (defect_on_le_profile H hs)

/- ## Transport along injective vertex maps -/

section Transport
variable [Fintype W]

theorem errors_card_le_of_injective {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (c : W → Bool) :
    (errors G (c ∘ f)).card ≤ (errors H c).card := by
  classical
  calc
    (errors G (c ∘ f)).card = ((errors G (c ∘ f)).image (Sym2.map f)).card :=
      (Finset.card_image_of_injective _ (Sym2.map.injective hf)).symm
    _ ≤ (errors H c).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      induction d using Sym2.inductionOn with
      | hf x y =>
        have hd' := (mem_errors G (c ∘ f) x y).mp hd
        exact (mem_errors H c (f x) (f y)).mpr ⟨f.map_adj hd'.1, hd'.2⟩

theorem defect_mono_of_injective {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) : defect G ≤ defect H := by
  obtain ⟨c, hc⟩ := exists_optimal H
  exact (defect_le_errors G (c ∘ f)).trans
    ((errors_card_le_of_injective f hf c).trans_eq hc)

theorem defect_mono_of_embedding {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) : defect G ≤ defect H :=
  defect_mono_of_injective f.toHom f.injective

theorem defect_on_map_le_of_injective {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (s : Finset V) :
    defect (on G s) ≤ defect (on H (s.map ⟨f, hf⟩)) := by
  let g : on G s →g on H (s.map ⟨f, hf⟩) :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        exact ⟨f.map_adj hxy.1, Finset.mem_map.mpr ⟨x, hxy.2.1, rfl⟩,
          Finset.mem_map.mpr ⟨y, hxy.2.2, rfl⟩⟩ }
  exact defect_mono_of_injective g hf

theorem defect_on_image_le_of_injective [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (s : Finset V) :
    defect (on G s) ≤ defect (on H (s.image f)) := by
  simpa only [Finset.map_eq_image] using defect_on_map_le_of_injective f hf s

theorem profile_mono_of_injective {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (n : ℕ) : profile G n ≤ profile H n := by
  apply (profile_le_iff G n (profile H n)).mpr
  intro s hs
  exact (defect_on_map_le_of_injective f hf s).trans
    (defect_on_le_profile H (by simpa only [Finset.card_map] using hs))

theorem profile_mono_of_embedding {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (n : ℕ) : profile G n ≤ profile H n :=
  profile_mono_of_injective f.toHom f.injective n

theorem defect_eq_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : defect G = defect H :=
  Nat.le_antisymm (defect_mono_of_injective f.toHom f.injective)
    (defect_mono_of_injective f.symm.toHom f.symm.injective)

theorem profile_eq_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (n : ℕ) : profile G n = profile H n :=
  Nat.le_antisymm (profile_mono_of_injective f.toHom f.injective n)
    (profile_mono_of_injective f.symm.toHom f.symm.injective n)

omit [Fintype V] [Fintype W] in
theorem badGraph_map (G : SimpleGraph V) (f : V ↪ W) (c : W → Bool) :
    badGraph (G.map f) c = (badGraph G (c ∘ f)).map f := by
  ext x y
  constructor
  · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hcol⟩
    exact ⟨a, b, ⟨hab, hcol⟩, rfl, rfl⟩
  · rintro ⟨a, b, ⟨hab, hcol⟩, rfl, rfl⟩
    exact ⟨⟨a, b, hab, rfl, rfl⟩, hcol⟩

theorem errors_map (G : SimpleGraph V) (f : V ↪ W) (c : W → Bool) :
    errors (G.map f) c = (errors G (c ∘ f)).map f.sym2Map := by
  classical
  simp only [errors]
  rw [badGraph_map]
  apply Finset.coe_injective
  simp only [SimpleGraph.coe_edgeFinset, Finset.coe_map]
  exact SimpleGraph.edgeSet_map f (badGraph G (c ∘ f))

@[simp] theorem errors_card_map (G : SimpleGraph V) (f : V ↪ W) (c : W → Bool) :
    (errors (G.map f) c).card = (errors G (c ∘ f)).card := by
  rw [errors_map, Finset.card_map]

/-- Adding isolated vertices, along any embedding, preserves the defect. -/
@[simp] theorem defect_map (G : SimpleGraph V) (f : V ↪ W) :
    defect (G.map f) = defect G := by
  apply Nat.le_antisymm
  · obtain ⟨c, hc⟩ := exists_optimal G
    let d : W → Bool := Function.extend f c (fun _ => false)
    have hd : d ∘ f = c := Function.extend_comp f.injective c (fun _ => false)
    calc
      defect (G.map f) ≤ (errors (G.map f) d).card := defect_le_errors _ d
      _ = (errors G c).card := by rw [errors_card_map, hd]
      _ = defect G := hc
  · exact defect_mono_of_embedding (SimpleGraph.Embedding.map f G)

omit [Fintype V] [Fintype W] in
theorem on_map (G : SimpleGraph V) (f : V ↪ W) (t : Finset W) :
    on (G.map f) t = (on G (t.preimage f f.injective.injOn)).map f := by
  ext x y
  constructor
  · rintro ⟨⟨a, b, hab, rfl, rfl⟩, ha, hb⟩
    exact ⟨a, b, ⟨hab, Finset.mem_preimage.mpr ha, Finset.mem_preimage.mpr hb⟩,
      rfl, rfl⟩
  · rintro ⟨a, b, ⟨hab, ha, hb⟩, rfl, rfl⟩
    exact ⟨⟨a, b, hab, rfl, rfl⟩, Finset.mem_preimage.mp ha, Finset.mem_preimage.mp hb⟩

omit [Fintype V] [Fintype W] in
@[simp] theorem on_map_map (G : SimpleGraph V) (f : V ↪ W) (s : Finset V) :
    on (G.map f) (s.map f) = (on G s).map f := by
  rw [on_map, Finset.preimage_map]

@[simp] theorem defect_on_map (G : SimpleGraph V) (f : V ↪ W) (s : Finset V) :
    defect (on (G.map f) (s.map f)) = defect (on G s) := by
  rw [on_map_map, defect_map]

/-- Adding isolated vertices also preserves every coordinate of the profile. -/
@[simp] theorem profile_map (G : SimpleGraph V) (f : V ↪ W) (n : ℕ) :
    profile (G.map f) n = profile G n := by
  classical
  apply Nat.le_antisymm
  · apply (profile_le_iff (G.map f) n (profile G n)).mpr
    intro t ht
    rw [on_map, defect_map]
    apply defect_on_le_profile G
    calc
      (t.preimage f f.injective.injOn).card ≤ t.card := by
        rw [Finset.card_preimage]
        exact Finset.card_filter_le _ _
      _ ≤ n := ht
  · exact profile_mono_of_embedding (SimpleGraph.Embedding.map f G) n

omit [Fintype V] [Fintype W] in
/-- An induced embedding identifies the restriction to a set with its image. -/
theorem map_on_eq_on_map {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (s : Finset V) :
    (on G s).map f.toEmbedding = on H (s.map f.toEmbedding) := by
  ext x y
  constructor
  · rintro ⟨a, b, ⟨hab, ha, hb⟩, rfl, rfl⟩
    exact ⟨f.map_adj_iff.mpr hab, Finset.mem_map.mpr ⟨a, ha, rfl⟩,
      Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩
  · rintro ⟨hxy, hx, hy⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact ⟨a, b, ⟨f.map_adj_iff.mp hxy, ha, hb⟩, rfl, rfl⟩

theorem defect_on_eq_of_embedding {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (s : Finset V) :
    defect (on G s) = defect (on H (s.map f.toEmbedding)) := by
  rw [← map_on_eq_on_map, defect_map]

theorem profile_on_eq_of_embedding {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (s : Finset V) (n : ℕ) :
    profile (on G s) n = profile (on H (s.map f.toEmbedding)) n := by
  rw [← map_on_eq_on_map, profile_map]

end Transport

/- ## Disjoint restrictions and saturation of optimal error sets -/

theorem errors_on_disjoint (G : SimpleGraph V) {s t : Finset V}
    (hst : Disjoint s t) (c : V → Bool) :
    Disjoint (errors (on G s) c) (errors (on G t) c) := by
  apply Finset.disjoint_left.mpr
  intro e hs ht
  induction e using Sym2.inductionOn with
  | hf x y =>
    exact Finset.disjoint_left.mp hst ((mem_errors_on G s c x y).mp hs).2.1
      ((mem_errors_on G t c x y).mp ht).2.1

theorem errors_on_union_card_le [DecidableEq V] (G : SimpleGraph V)
    {s t : Finset V} (hst : Disjoint s t) (c : V → Bool) :
    (errors (on G s) c).card + (errors (on G t) c).card ≤
      (errors (on G (s ∪ t)) c).card := by
  classical
  rw [← Finset.card_union_of_disjoint (errors_on_disjoint G hst c)]
  apply Finset.card_le_card
  exact Finset.union_subset
    (errors_on_mono G Finset.subset_union_left c)
    (errors_on_mono G Finset.subset_union_right c)

/-- Frustration is superadditive on vertex-disjoint induced restrictions;
    edges between the two sets need not be absent. -/
theorem defect_on_union_ge [DecidableEq V] (G : SimpleGraph V)
    {s t : Finset V} (hst : Disjoint s t) :
    defect (on G s) + defect (on G t) ≤ defect (on G (s ∪ t)) := by
  obtain ⟨c, hc⟩ := exists_optimal (on G (s ∪ t))
  calc
    defect (on G s) + defect (on G t) ≤
        (errors (on G s) c).card + (errors (on G t) c).card :=
      Nat.add_le_add (defect_le_errors _ c) (defect_le_errors _ c)
    _ ≤ (errors (on G (s ∪ t)) c).card := errors_on_union_card_le G hst c
    _ = defect (on G (s ∪ t)) := hc

/-- If a smaller graph already has the full defect, every error of an
    optimal coloring of the larger graph is an edge of the smaller graph. -/
theorem errors_eq_of_defect_eq {G H : SimpleGraph V} (hGH : G ≤ H)
    (hdef : defect G = defect H) {c : V → Bool}
    (hc : (errors H c).card = defect H) : errors G c = errors H c := by
  apply Finset.eq_of_subset_of_card_le (errors_mono hGH c)
  calc
    (errors H c).card = defect H := hc
    _ = defect G := hdef.symm
    _ ≤ (errors G c).card := defect_le_errors G c

theorem errors_on_eq_of_defect_eq (G : SimpleGraph V) {s q : Finset V}
    (hsq : s ⊆ q) (hdef : defect (on G s) = defect (on G q))
    {c : V → Bool} (hc : (errors (on G q) c).card = defect (on G q)) :
    errors (on G q) c = errors (on G s) c :=
  (errors_eq_of_defect_eq (on_mono_set G hsq) hdef hc).symm

theorem optimal_errors_inside (G : SimpleGraph V) {s q : Finset V}
    (hsq : s ⊆ q) (hdef : defect (on G s) = defect (on G q))
    {c : V → Bool} (hc : (errors (on G q) c).card = defect (on G q))
    {x y : V} (hxy : (on G q).Adj x y) (hcol : c x = c y) : x ∈ s ∧ y ∈ s := by
  have he : s(x, y) ∈ errors (on G q) c := (mem_errors _ c x y).mpr ⟨hxy, hcol⟩
  rw [errors_on_eq_of_defect_eq G hsq hdef hc] at he
  exact ⟨((mem_errors_on G s c x y).mp he).2.1,
    ((mem_errors_on G s c x y).mp he).2.2.1⟩

/-- A disjoint part of a saturated restriction must be bipartite. -/
theorem defect_on_eq_zero_of_saturation (G : SimpleGraph V) {s t q : Finset V}
    (hst : Disjoint s t) (hsq : s ⊆ q) (htq : t ⊆ q)
    (hdef : defect (on G s) = defect (on G q)) : defect (on G t) = 0 := by
  classical
  have h := (defect_on_union_ge G hst).trans
    (defect_on_mono G (Finset.union_subset hsq htq))
  omega

/- ## Error endpoints and a four-color repair -/

/-- The endpoints of the monochromatic edges of a binary assignment. -/
noncomputable def errorVertices (G : SimpleGraph V) (c : V → Bool) : Finset V := by
  classical
  exact (errors G c).biUnion Sym2.toFinset

@[simp] theorem mem_errorVertices (G : SimpleGraph V) (c : V → Bool) (x : V) :
    x ∈ errorVertices G c ↔ ∃ e ∈ errors G c, x ∈ e := by
  classical
  simp [errorVertices]

theorem left_mem_errorVertices {G : SimpleGraph V} {c : V → Bool} {x y : V}
    (h : s(x, y) ∈ errors G c) : x ∈ errorVertices G c := by
  exact (mem_errorVertices G c x).mpr ⟨s(x, y), h, by simp⟩

theorem right_mem_errorVertices {G : SimpleGraph V} {c : V → Bool} {x y : V}
    (h : s(x, y) ∈ errors G c) : y ∈ errorVertices G c := by
  exact (mem_errorVertices G c y).mpr ⟨s(x, y), h, by simp⟩

theorem error_endpoints_mem {G : SimpleGraph V} {c : V → Bool} {x y : V}
    (hxy : G.Adj x y) (hcol : c x = c y) :
    x ∈ errorVertices G c ∧ y ∈ errorVertices G c := by
  have he := (mem_errors G c x y).mpr ⟨hxy, hcol⟩
  exact ⟨left_mem_errorVertices he, right_mem_errorVertices he⟩

theorem errorVertices_card_le (G : SimpleGraph V) (c : V → Bool) :
    (errorVertices G c).card ≤ 2 * (errors G c).card := by
  classical
  rw [errorVertices, Nat.mul_comm 2]
  apply Finset.card_biUnion_le_card_mul
  intro e _
  rw [Sym2.card_toFinset]
  split_ifs <;> omega

theorem errorVertices_on_subset (G : SimpleGraph V) (s : Finset V) (c : V → Bool) :
    errorVertices (on G s) c ⊆ s := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := (mem_errorVertices (on G s) c x).mp hx
  induction e using Sym2.inductionOn with
  | hf a b =>
    have he' := (mem_errors_on G s c a b).mp he
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact he'.2.1
    · exact he'.2.2.1

theorem errorVertices_on_subset_of_defect_eq (G : SimpleGraph V) {s q : Finset V}
    (hsq : s ⊆ q) (hdef : defect (on G s) = defect (on G q))
    {c : V → Bool} (hc : (errors (on G q) c).card = defect (on G q)) :
    errorVertices (on G q) c ⊆ s := by
  classical
  have he : errorVertices (on G q) c = errorVertices (on G s) c := by
    unfold errorVertices
    rw [errors_on_eq_of_defect_eq G hsq hdef hc]
  rw [he]
  exact errorVertices_on_subset G s c

/-- An optimal coloring has an error-endpoint set of size at most twice its defect. -/
theorem exists_optimal_endpoints (G : SimpleGraph V) :
    ∃ (c : V → Bool) (s : Finset V), (errors G c).card = defect G ∧
      s.card ≤ 2 * defect G ∧
      ∀ ⦃x y⦄, G.Adj x y → c x = c y → x ∈ s ∧ y ∈ s := by
  obtain ⟨c, hc⟩ := exists_optimal G
  refine ⟨c, errorVertices G c, hc, ?_, fun {_ _} hxy hcol => error_endpoints_mem hxy hcol⟩
  simpa only [hc] using errorVertices_card_le G c

omit [Fintype V] in
/-- Keep the original two colors off the cover and use two new colors on it.
    This explicit construction is valid even when the cover or the vertex type is empty. -/
noncomputable def fourColoringOfErrorCover (G : SimpleGraph V) (s : Finset V)
    (c b : V → Bool)
    (hb : ∀ ⦃x y⦄, (on G s).Adj x y → b x ≠ b y)
    (hcover : ∀ ⦃x y⦄, G.Adj x y → c x = c y → x ∈ s ∧ y ∈ s) :
    G.Coloring (Bool × Bool) := by
  classical
  let d : V → Bool × Bool := fun x => if x ∈ s then (true, b x) else (false, c x)
  refine SimpleGraph.Coloring.mk d ?_
  intro x y hxy heq
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · exact hb ⟨hxy, hx, hy⟩ (by simpa [d, hx, hy] using heq)
  · simp [d, hx, hy] at heq
  · simp [d, hx, hy] at heq
  · have hc : c x = c y := by simpa [d, hx, hy] using heq
    exact hx (hcover hxy hc).1

theorem colorable_four_of_error_cover (G : SimpleGraph V) (s : Finset V)
    (c : V → Bool)
    (hcover : ∀ ⦃x y⦄, G.Adj x y → c x = c y → x ∈ s ∧ y ∈ s)
    (hs : defect (on G s) = 0) : G.Colorable 4 := by
  obtain ⟨b, hb⟩ := (defect_zero_iff (on G s)).mp hs
  simpa using (fourColoringOfErrorCover G s c b (fun {_ _} hxy => hb hxy)
    (fun {_ _} hxy hcol => hcover hxy hcol)).colorable

theorem colorable_four_of_errorVertices (G : SimpleGraph V) (c : V → Bool)
    (h : defect (on G (errorVertices G c)) = 0) : G.Colorable 4 :=
  colorable_four_of_error_cover G (errorVertices G c) c
    (fun {_ _} hxy hcol => error_endpoints_mem hxy hcol) h

/-- A graph that is not four-colorable and has defect at most `B` already
    has positive defect on a set of at most `2 * B` vertices. -/
theorem profile_pos_of_not_colorable_four (G : SimpleGraph V) {B : ℕ}
    (hG : ¬ G.Colorable 4) (hB : defect G ≤ B) : 0 < profile G (2 * B) := by
  obtain ⟨c, hc⟩ := exists_optimal G
  have hs : (errorVertices G c).card ≤ 2 * B :=
    (errorVertices_card_le G c).trans (Nat.mul_le_mul_left 2 (hc.trans_le hB))
  have hp : 0 < defect (on G (errorVertices G c)) := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hG (colorable_four_of_errorVertices G c h)
  exact hp.trans_le (defect_on_le_profile G hs)

end Finite
end E74

/-
# Finite branching for bounded-width obstructions

A family of finite sets has a bounded finite witness to the absence of a set of
size at most `t`, provided every partial support of size at most `t` has a
bounded-width obstruction. No finiteness assumption on the ambient type is used.
-/

namespace E74
namespace Witness

universe u

/-- A deliberately nonoptimal bound for the number of variables retained by
bounded-width branching. The second argument is the total support budget, and
the third is the remaining branching depth. -/
def branchBound (k t : ℕ) : ℕ → ℕ
  | 0 => t + k
  | n + 1 => t + k + k * branchBound k t n

/-- Bounded-width branching, with an already selected support `F`. -/
theorem bounded_branching_aux {α : Type u} [DecidableEq α] (k t : ℕ) (P : Finset α → Prop)
    (h : ∀ F : Finset α, F.card ≤ t →
      ∃ R : Finset α, R.card ≤ k ∧
        ∀ E : Finset α, P E → F ⊆ E → ∃ e ∈ R, e ∈ E ∧ e ∉ F)
    (n : ℕ) (F : Finset α) (hFn : F.card + n = t) :
    ∃ T : Finset α, F ⊆ T ∧ T.card ≤ branchBound k t n ∧
      ∀ E : Finset α, P E → F ⊆ E → t < (E ∩ T).card := by
  classical
  induction n generalizing F with
  | zero =>
    obtain ⟨R, hR, hRE⟩ := h F (by omega)
    refine ⟨F ∪ R, Finset.subset_union_left, ?_, ?_⟩
    · exact (Finset.card_union_le F R).trans (by dsimp [branchBound]; omega)
    · intro E hE hFE
      obtain ⟨e, heR, heE, heF⟩ := hRE E hE hFE
      have hsub : insert e F ⊆ E ∩ (F ∪ R) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_inter.mpr ⟨heE, Finset.mem_union_right F heR⟩
        · exact Finset.mem_inter.mpr ⟨hFE ha, Finset.mem_union_left R ha⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem heF] at hc
      omega
  | succ n ih =>
    obtain ⟨R, hR, hRE⟩ := h F (by omega)
    have hchild : ∀ e : ↥(R \ F), ∃ T : Finset α,
        insert e.val F ⊆ T ∧ T.card ≤ branchBound k t n ∧
        ∀ E : Finset α, P E → insert e.val F ⊆ E → t < (E ∩ T).card := by
      intro e
      apply ih (insert e.val F)
      rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp e.prop).2]
      omega
    choose child hchildF hchildcard hchildE using hchild
    let U : Finset α := (R \ F).attach.biUnion child
    have hU : U.card ≤ k * branchBound k t n := by
      calc
        U.card ≤ (R \ F).attach.card * branchBound k t n := by
          apply Finset.card_biUnion_le_card_mul
          intro e _
          exact hchildcard e
        _ ≤ k * branchBound k t n := by
          rw [Finset.card_attach]
          exact Nat.mul_le_mul_right _ ((Finset.card_le_card Finset.sdiff_subset).trans hR)
    refine ⟨(F ∪ R) ∪ U, Finset.subset_union_left.trans Finset.subset_union_left, ?_, ?_⟩
    · calc
        ((F ∪ R) ∪ U).card ≤ (F ∪ R).card + U.card := Finset.card_union_le _ _
        _ ≤ F.card + R.card + U.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ t + k + k * branchBound k t n := by omega
        _ = branchBound k t (n + 1) := rfl
    · intro E hE hFE
      obtain ⟨e, heR, heE, heF⟩ := hRE E hE hFE
      let e' : ↥(R \ F) := ⟨e, Finset.mem_sdiff.mpr ⟨heR, heF⟩⟩
      have hinsert : insert e'.val F ⊆ E := Finset.insert_subset heE hFE
      have hsmall := hchildE e' E hE hinsert
      apply hsmall.trans_le
      apply Finset.card_le_card
      intro a ha
      rcases Finset.mem_inter.mp ha with ⟨haE, haT⟩
      refine Finset.mem_inter.mpr ⟨haE, Finset.mem_union_right _ ?_⟩
      exact Finset.mem_biUnion.mpr ⟨e', Finset.mem_attach _ _, haT⟩

/-- A bounded finite set of variables detects that every member of `P` has more
than `t` variables. The hypothesis provides a width-`k` set of possible next
variables for every partial support of size at most `t`. -/
theorem bounded_branching {α : Type u} [DecidableEq α] (k t : ℕ) (P : Finset α → Prop)
    (h : ∀ F : Finset α, F.card ≤ t →
      ∃ R : Finset α, R.card ≤ k ∧
        ∀ E : Finset α, P E → F ⊆ E → ∃ e ∈ R, e ∈ E ∧ e ∉ F) :
    ∃ T : Finset α, T.card ≤ branchBound k t t ∧
      ∀ E : Finset α, P E → t < (E ∩ T).card := by
  classical
  obtain ⟨T, _, hT, hTE⟩ := bounded_branching_aux k t P h t ∅ (by simp)
  exact ⟨T, hT, fun E hE => hTE E hE (Finset.empty_subset _)⟩

end Witness
end E74

/-
# Short root-path XOR obstructions

Root paths of length at most `D` turn a failed binary coloring into a constraint
supported on at most `2 * D + 1` actual edges. Repeated vertices and repeated
edges are allowed: the XOR is evaluated on the walk, while the certificate is
the finite set of edges supporting it. A cycle basis is not needed.
-/

namespace E74
namespace Witness

open SimpleGraph
universe u
variable {V : Type u}

/-- The bit change along a walk, with edges of `F` prescribed to have equal
endpoint bits and all other edges prescribed to have different bits. -/
noncomputable def walkPhase {G : SimpleGraph V} (F : Finset (Sym2 V))
    {a b : V} (p : G.Walk a b) : Bool := by
  classical
  exact p.edges.foldr (fun e z => decide (e ∉ F) ^^ z) false

/-- The prescribed bit changes telescope along any walk on which a coloring
realizes the prescribed equalities. -/
theorem walkPhase_eq {G : SimpleGraph V} (F : Finset (Sym2 V))
    {a b : V} (p : G.Walk a b) (c : V → Bool)
    (h : ∀ x y, s(x, y) ∈ p.edges → (s(x, y) ∈ F ↔ c x = c y)) :
    walkPhase F p = (c a ^^ c b) := by
  classical
  induction p with
  | nil => simp [walkPhase]
  | @cons a b z hab p ih =>
    have hhead : s(a, b) ∈ F ↔ c a = c b := h a b (by simp)
    have htail : walkPhase F p = (c b ^^ c z) :=
      ih (fun x y he => h x y (by simp [he]))
    have hbit : decide (s(a, b) ∉ F) = (c a ^^ c b) := by
      cases ha : c a <;> cases hb : c b <;> simp_all
    change (decide (s(a, b) ∉ F) ^^ walkPhase F p) = (c a ^^ c z)
    rw [hbit, htail]
    cases c a <;> cases c b <;> cases c z <;> rfl

/-- Every partial error support of size at most `t` has a short obstruction.
For any actual coloring extending this support, at least one new error lies in
the obstruction. The bound is uniform over disconnected graphs as well. -/
theorem short_error_certificate [Fintype V] (G : SimpleGraph V) (D t : ℕ)
    (hD : ∀ a b, G.Reachable a b → ∃ p : G.Walk a b, p.length ≤ D)
    (ht : t < defect G) (F : Finset (Sym2 V)) (hF : F.card ≤ t) :
    ∃ R : Finset (Sym2 V), R.card ≤ 2 * D + 1 ∧
      ∀ c : V → Bool, F ⊆ errors G c → ∃ e ∈ R, e ∈ errors G c ∧ e ∉ F := by
  classical
  let root : V → V := fun v => (G.connectedComponentMk v).out
  have hroot (v : V) : G.Reachable (root v) v :=
    ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk v))
  choose path hpath using fun v => hD (root v) v (hroot v)
  let c₀ : V → Bool := fun v => walkPhase F (path v)
  have hnot : ¬ errors G c₀ ⊆ F := by
    intro hsub
    have := (defect_le_errors G c₀).trans ((Finset.card_le_card hsub).trans hF)
    omega
  obtain ⟨e, he, heF⟩ := Finset.not_subset.mp hnot
  induction e using Sym2.inductionOn with
  | hf a b =>
    obtain ⟨hab, heq⟩ := (mem_errors G c₀ a b).mp he
    let R : Finset (Sym2 V) :=
      insert s(a, b) ((path a).edges.toFinset ∪ (path b).edges.toFinset)
    have hRa : (path a).edges.toFinset ⊆ R := by
      intro e he
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
    have hRb : (path b).edges.toFinset ⊆ R := by
      intro e he
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ he)
    refine ⟨R, ?_, ?_⟩
    · have ha : (path a).edges.toFinset.card ≤ D :=
        (List.toFinset_card_le _).trans (by simpa using hpath a)
      have hb : (path b).edges.toFinset.card ≤ D :=
        (List.toFinset_card_le _).trans (by simpa using hpath b)
      have hi := Finset.card_insert_le s(a, b)
        ((path a).edges.toFinset ∪ (path b).edges.toFinset)
      have hu := Finset.card_union_le (path a).edges.toFinset (path b).edges.toFinset
      dsimp only [R]
      omega
    · intro c hFc
      by_contra hno
      push_neg at hno
      have hphase (v : V) (hv : (path v).edges.toFinset ⊆ R) :
          walkPhase F (path v) = (c (root v) ^^ c v) := by
        apply walkPhase_eq
        intro x y hxy
        constructor
        · intro hf
          exact ((mem_errors G c x y).mp (hFc hf)).2
        · intro hc
          exact hno _ (hv (List.mem_toFinset.mpr hxy))
            ((mem_errors G c x y).mpr ⟨(path v).adj_of_mem_edges hxy, hc⟩)
      have hrab : root a = root b :=
        congrArg (fun q : G.ConnectedComponent => q.out) (ConnectedComponent.sound hab.reachable)
      change walkPhase F (path a) = walkPhase F (path b) at heq
      rw [hphase a hRa, hphase b hRb, hrab] at heq
      have hcab : c a = c b := Bool.xor_right_inj.mp heq
      exact heF (hno s(a, b) (by simp [R]) ((mem_errors G c a b).mpr ⟨hab, hcab⟩))

end Witness
end E74

/-
# Uniform finite witnesses for binary-coloring defect

If all connected components have diameter at most `D`, then defect greater than
`t` is witnessed on a vertex set bounded solely in terms of `D` and `t`.

The proof uses short root-path XOR obstructions and finite support branching.
It works for arbitrary vertex universes and disconnected graphs, including the
empty vertex type. The explicit recursive bound is intentionally nonoptimal.
-/

namespace E74

open SimpleGraph
universe u
variable {V : Type u}

/-- A uniform (nonoptimized) bound on the number of vertices in a witness. -/
def witnessBound (D t : ℕ) : ℕ :=
  2 * Witness.branchBound (2 * D + 1) t t

/-- Explicit-bound form of the bounded-diameter witness lemma. -/
theorem exists_bounded_diameter_witness [Fintype V] (G : SimpleGraph V) (D t : ℕ)
    (hD : ∀ a b, G.Reachable a b → ∃ p : G.Walk a b, p.length ≤ D)
    (ht : t < defect G) :
    ∃ s : Finset V, s.card ≤ witnessBound D t ∧ t < defect (on G s) := by
  classical
  obtain ⟨T, hT, hTE⟩ := Witness.bounded_branching (2 * D + 1) t
    (fun E : Finset (Sym2 V) => ∃ c : V → Bool, errors G c = E) (by
      intro F hF
      obtain ⟨R, hR, hRE⟩ := Witness.short_error_certificate G D t hD ht F hF
      refine ⟨R, hR, ?_⟩
      rintro E ⟨c, rfl⟩ hFc
      exact hRE c hFc)
  let s : Finset V := T.biUnion Sym2.toFinset
  have hs : s.card ≤ 2 * T.card := by
    rw [Nat.mul_comm 2]
    apply Finset.card_biUnion_le_card_mul
    intro e _
    rw [Sym2.card_toFinset]
    split <;> omega
  refine ⟨s, hs.trans (Nat.mul_le_mul_left 2 hT), ?_⟩
  obtain ⟨c, hc⟩ := exists_optimal (on G s)
  have hsub : errors G c ∩ T ⊆ errors (on G s) c := by
    intro e he
    obtain ⟨heG, heT⟩ := Finset.mem_inter.mp he
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨hab, hcab⟩ := (mem_errors G c a b).mp heG
      apply (mem_errors_on G s c a b).mpr
      refine ⟨hab, ?_, ?_, hcab⟩
      · exact Finset.mem_biUnion.mpr ⟨s(a, b), heT, by simp [Sym2.toFinset_mk_eq]⟩
      · exact Finset.mem_biUnion.mpr ⟨s(a, b), heT, by simp [Sym2.toFinset_mk_eq]⟩
  have hlarge := (hTE (errors G c) ⟨c, rfl⟩).trans_le (Finset.card_le_card hsub)
  simpa only [hc] using hlarge

/-- Uniform finite witness bound for graphs with bounded component diameter.
The bound is chosen before the vertex type and graph, and the statement is
universe-polymorphic. -/
theorem bounded_diameter_witness (D t : ℕ) :
    ∃ M : ℕ, ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      (∀ a b, G.Reachable a b → ∃ p : G.Walk a b, p.length ≤ D) →
      t < defect G →
      ∃ s : Finset V, s.card ≤ M ∧ t < defect (on G s) := by
  exact ⟨witnessBound D t, fun V _ G hD ht => exists_bounded_diameter_witness G D t hD ht⟩

end E74

/-
# Finite-source graph geometry

`near G S r` is the finite set of vertices reachable from `S` by a walk of
length at most `r`.  `height G S R` is the minimum such radius, truncated at
`R + 1`; in particular disconnected vertices have height `R + 1`, not zero.

The principal bound is `near_component_diameter`: the components of
`on G (near G S R)` have diameter at most `S.card * (2 * R + 1)`, independently
of the number of vertices of `G`.  The full vertex type is retained by `on`,
so vertices outside the neighborhood are isolated and use the nil walk.
-/

namespace E74

open SimpleGraph
universe u
variable {V : Type u}

/-- The radius-`r` neighborhood of a finite source set, using genuine walks. -/
noncomputable def near [Fintype V] (G : SimpleGraph V) (S : Finset V) (r : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v => ∃ s ∈ S, ∃ p : G.Walk s v, p.length ≤ r

/-- Minimum distance from `S`, with sentinel `R + 1` for far or disconnected
vertices.  It does not use the zero-valued distance of disconnected pairs. -/
noncomputable def height [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) (v : V) : ℕ := by
  classical
  exact Nat.find (show ∃ n : ℕ, v ∈ near G S n ∨ n = R + 1 from
    ⟨R + 1, Or.inr rfl⟩)

@[simp] theorem mem_near [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (r : ℕ) (v : V) :
    v ∈ near G S r ↔ ∃ s ∈ S, ∃ p : G.Walk s v, p.length ≤ r := by
  classical
  simp [near]

/-- Every source belongs to every nonnegative-radius neighborhood. -/
theorem subset_near [Fintype V] (G : SimpleGraph V) (S : Finset V) (r : ℕ) :
    S ⊆ near G S r := by
  intro v hv
  exact (mem_near G S r v).2 ⟨v, hv, .nil, Nat.zero_le _⟩

/-- Simultaneous monotonicity in the source set and the radius. -/
theorem near_mono [Fintype V] (G : SimpleGraph V) {S T : Finset V} {r q : ℕ}
    (hST : S ⊆ T) (hrq : r ≤ q) : near G S r ⊆ near G T q := by
  intro v hv
  obtain ⟨s, hs, p, hp⟩ := (mem_near G S r v).1 hv
  exact (mem_near G T q v).2 ⟨s, hST hs, p, hp.trans hrq⟩

theorem near_mono_radius [Fintype V] (G : SimpleGraph V) (S : Finset V)
    {r q : ℕ} (hrq : r ≤ q) : near G S r ⊆ near G S q :=
  near_mono G (Finset.Subset.refl S) hrq

/-- Traversing an edge increases the needed radius by at most one. -/
theorem adj_mem_near_succ [Fintype V] (G : SimpleGraph V) (S : Finset V)
    {r : ℕ} {a b : V} (ha : a ∈ near G S r) (hab : G.Adj a b) :
    b ∈ near G S (r + 1) := by
  obtain ⟨s, hs, p, hp⟩ := (mem_near G S r a).1 ha
  exact (mem_near G S (r + 1) b).2
    ⟨s, hs, p.concat hab, by simpa using Nat.add_le_add_right hp 1⟩

@[simp] theorem near_empty [Fintype V] (G : SimpleGraph V) (r : ℕ) :
    near G ∅ r = ∅ := by
  classical
  ext v
  simp

@[simp] theorem near_zero [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    near G S 0 = S := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨s, hs, p, hp⟩ := (mem_near G S 0 v).1 hv
    have heq : s = v := p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)
    simpa [← heq] using hs
  · exact subset_near G S 0

/-- Restrict a walk to `on G U`, when its support lies in `U`. -/
def walkOn {G : SimpleGraph V} (U : Finset V) {a b : V} :
    (p : G.Walk a b) → (∀ v ∈ p.support, v ∈ U) → (on G U).Walk a b
  | .nil, _ => .nil
  | .cons h p, hp =>
    .cons ⟨h, hp _ (by simp), hp _ (by simp)⟩
      (walkOn U p (fun v hv => hp v (by simp [hv])))

@[simp] theorem length_walkOn {G : SimpleGraph V} (U : Finset V) {a b : V}
    (p : G.Walk a b) (hp : ∀ v ∈ p.support, v ∈ U) :
    (walkOn U p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [walkOn, ih]

/-- Every vertex on a short source walk is still in the neighborhood. -/
theorem support_subset_near [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) {s v : V} (hs : s ∈ S) (p : G.Walk s v) (hp : p.length ≤ R) :
    ∀ x ∈ p.support, x ∈ near G S R := by
  classical
  intro x hx
  exact (mem_near G S R x).2
    ⟨s, hs, p.takeUntil x hx, (p.length_takeUntil_le hx).trans hp⟩

/-- A neighborhood vertex has a short source walk entirely in the neighborhood. -/
theorem exists_root_walk [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) {v : V} (hv : v ∈ near G S R) :
    ∃ s ∈ S, ∃ p : (on G (near G S R)).Walk s v, p.length ≤ R := by
  obtain ⟨s, hs, p, hp⟩ := (mem_near G S R v).1 hv
  exact ⟨s, hs, walkOn _ p (support_subset_near G S R hs p hp), by simpa using hp⟩

/- ## Diameter from a finite root cover -/

/-- The finite contact graph on roots: an edge can be expanded to a short walk. -/
private def rootContact (Q : SimpleGraph V) (S : Finset V) (L : ℕ) :
    SimpleGraph S where
  Adj s t := s ≠ t ∧ ∃ p : Q.Walk s t, p.length ≤ L
  symm := by
    rintro s t ⟨hne, p, hp⟩
    exact ⟨hne.symm, p.reverse, by simpa using hp⟩
  loopless := by intro s h; exact h.1 rfl

private theorem rootContact_reachable (Q : SimpleGraph V) (S : Finset V) (L : ℕ)
    {s t : S} (p : Q.Walk s t) (hp : p.length ≤ L) :
    (rootContact Q S L).Reachable s t := by
  classical
  by_cases hst : s = t
  · subst t
    exact .rfl
  · exact (show (rootContact Q S L).Adj s t from ⟨hst, p, hp⟩).reachable

/-- Expanding a contact walk costs at most `L` per edge. -/
private theorem rootContact_expand (Q : SimpleGraph V) (S : Finset V) (L : ℕ)
    {s t : S} (p : (rootContact Q S L).Walk s t) :
    ∃ q : Q.Walk s t, q.length ≤ p.length * L := by
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | cons h p ih =>
    obtain ⟨r, hr⟩ := h.2
    obtain ⟨q, hq⟩ := ih
    refine ⟨r.append q, ?_⟩
    simp only [Walk.length_append, Walk.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A walk in the covered graph induces connectivity of any chosen endpoint roots. -/
private theorem rootContact_connected_of_walk (G : SimpleGraph V) (U S : Finset V)
    (R : ℕ)
    (hcover : ∀ v ∈ U, ∃ s ∈ S, ∃ p : (on G U).Walk s v, p.length ≤ R)
    {a b : V} (p : (on G U).Walk a b) :
    ∀ (s t : S) (ps : (on G U).Walk s a) (pt : (on G U).Walk t b),
      ps.length ≤ R → pt.length ≤ R →
      (rootContact (on G U) S (2 * R + 1)).Reachable s t := by
  induction p with
  | nil =>
    intro s t ps pt hps hpt
    apply rootContact_reachable _ _ _ (ps.append pt.reverse)
    simp only [Walk.length_append, Walk.length_reverse]
    omega
  | @cons a x b hax p ih =>
    intro s t ps pt hps hpt
    obtain ⟨r, hr, pr, hpr⟩ := hcover x hax.2.2
    let r' : S := ⟨r, hr⟩
    have hsr : (rootContact (on G U) S (2 * R + 1)).Reachable s r' := by
      apply rootContact_reachable _ _ _ (ps.append (hax.toWalk.append pr.reverse))
      simp only [Walk.length_append, Walk.length_reverse]
      change ps.length + (1 + pr.length) ≤ 2 * R + 1
      omega
    exact hsr.trans (ih r' t pr pt hpr hpt)

/-- A graph covered by short root walks has bounded component diameter.

Only the finite number of roots enters the bound; `U` may be arbitrarily large.
The graph `on G U` retains all vertices, and the proof also handles its isolated
vertices outside `U` (and the case of an empty root set). -/
theorem on_component_diameter_of_cover (G : SimpleGraph V) (U S : Finset V) (R : ℕ)
    (hcover : ∀ v ∈ U, ∃ s ∈ S, ∃ p : (on G U).Walk s v, p.length ≤ R)
    (a b : V) (hab : (on G U).Reachable a b) :
    ∃ p : (on G U).Walk a b, p.length ≤ S.card * (2 * R + 1) := by
  classical
  obtain ⟨p⟩ := hab
  by_cases heq : a = b
  · subst b
    exact ⟨.nil, by simp⟩
  have ha : a ∈ U := by
    cases p with
    | nil => exact (heq rfl).elim
    | cons h _ => exact h.2.1
  have hb : b ∈ U := by
    have hne : b ≠ a := Ne.symm heq
    cases p.reverse with
    | nil => exact (hne rfl).elim
    | cons h _ => exact h.2.1
  obtain ⟨s, hs, ps, hps⟩ := hcover a ha
  obtain ⟨t, ht, pt, hpt⟩ := hcover b hb
  let s' : S := ⟨s, hs⟩
  let t' : S := ⟨t, ht⟩
  have hst := rootContact_connected_of_walk G U S R hcover p s' t' ps pt hps hpt
  obtain ⟨c, hc⟩ := hst.exists_isPath
  have hlen : c.length + 1 ≤ S.card := by
    simpa only [Fintype.card_coe] using Nat.succ_le_of_lt hc.length_lt
  obtain ⟨q, hq⟩ := rootContact_expand (on G U) S (2 * R + 1) c
  refine ⟨ps.reverse.append (q.append pt), ?_⟩
  calc
    (ps.reverse.append (q.append pt)).length = ps.length + q.length + pt.length := by
      simp [Nat.add_assoc]
    _ ≤ R + c.length * (2 * R + 1) + R := by omega
    _ ≤ (c.length + 1) * (2 * R + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    _ ≤ S.card * (2 * R + 1) := Nat.mul_le_mul_right _ hlen

/-- Finite-source neighborhood component diameter, independent of `Fintype.card V`.
This is the bounded-walk interface consumed by the bounded-diameter witness lemma. -/
theorem near_component_diameter [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) (a b : V) (hab : (on G (near G S R)).Reachable a b) :
    ∃ p : (on G (near G S R)).Walk a b, p.length ≤ S.card * (2 * R + 1) :=
  on_component_diameter_of_cover G (near G S R) S R
    (fun _ hv => exists_root_walk G S R hv) a b hab

/-- The uniform version with an a priori bound on the number of sources. -/
theorem near_component_diameter_le [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R N : ℕ) (hS : S.card ≤ N) (a b : V)
    (hab : (on G (near G S R)).Reachable a b) :
    ∃ p : (on G (near G S R)).Walk a b, p.length ≤ N * (2 * R + 1) := by
  obtain ⟨p, hp⟩ := near_component_diameter G S R a b hab
  exact ⟨p, hp.trans (Nat.mul_le_mul_right _ hS)⟩

/- ## Sentinel-safe height -/

/-- A height is either witnessed by a walk or is the sentinel. -/
theorem height_spec [Fintype V] (G : SimpleGraph V) (S : Finset V) (R : ℕ) (v : V) :
    v ∈ near G S (height G S R v) ∨ height G S R v = R + 1 := by
  classical
  exact Nat.find_spec (p := fun n => v ∈ near G S n ∨ n = R + 1) _

/-- All heights, including those of disconnected vertices, are at most the sentinel. -/
theorem height_le [Fintype V] (G : SimpleGraph V) (S : Finset V) (R : ℕ) (v : V) :
    height G S R v ≤ R + 1 := by
  classical
  exact Nat.find_min' _ (Or.inr rfl)

theorem height_le_of_mem_near [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) {r : ℕ} {v : V} (hv : v ∈ near G S r) : height G S R v ≤ r := by
  classical
  exact Nat.find_min' _ (Or.inl hv)

/-- Below the sentinel, height bounds are exactly neighborhood membership. -/
theorem height_le_iff_mem_near [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) {r : ℕ} (hr : r ≤ R) (v : V) :
    height G S R v ≤ r ↔ v ∈ near G S r := by
  constructor
  · intro hv
    rcases height_spec G S R v with hnear | hsentinel
    · exact near_mono_radius G S hv hnear
    · omega
  · exact height_le_of_mem_near G S R

/-- Precisely the vertices outside radius `R` receive the sentinel `R + 1`. -/
theorem height_eq_sentinel_iff [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) (v : V) : height G S R v = R + 1 ↔ v ∉ near G S R := by
  constructor
  · intro hv hnear
    have hh := height_le_of_mem_near G S R hnear
    omega
  · intro hv
    have hle := height_le G S R v
    have hn : ¬ height G S R v ≤ R := by
      intro hh
      exact hv ((height_le_iff_mem_near G S R (Nat.le_refl R) v).1 hh)
    omega

@[simp] theorem height_eq_zero_iff [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R : ℕ) (v : V) : height G S R v = 0 ↔ v ∈ S := by
  simpa using height_le_iff_mem_near G S R (Nat.zero_le R) v

@[simp] theorem height_empty [Fintype V] (G : SimpleGraph V) (R : ℕ) (v : V) :
    height G ∅ R v = R + 1 := by
  apply (height_eq_sentinel_iff G ∅ R v).2
  simp

/-- In particular, vertices disconnected from every source are never assigned zero. -/
theorem height_eq_sentinel_of_not_reachable [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (R : ℕ) (v : V) (hv : ∀ s ∈ S, ¬ G.Reachable s v) :
    height G S R v = R + 1 := by
  apply (height_eq_sentinel_iff G S R v).2
  intro hnear
  obtain ⟨s, hs, p, _⟩ := (mem_near G S R v).1 hnear
  exact hv s hs p.reachable

/-- Height changes by at most one across an edge, including at the sentinel. -/
theorem height_adj_le [Fintype V] (G : SimpleGraph V) (S : Finset V) (R : ℕ)
    {a b : V} (hab : G.Adj a b) : height G S R b ≤ height G S R a + 1 := by
  rcases height_spec G S R a with ha | ha
  · exact height_le_of_mem_near G S R (adj_mem_near_succ G S ha hab)
  · have hb := height_le G S R b
    omega

theorem height_adj [Fintype V] (G : SimpleGraph V) (S : Finset V) (R : ℕ)
    {a b : V} (hab : G.Adj a b) :
    height G S R a ≤ height G S R b + 1 ∧ height G S R b ≤ height G S R a + 1 :=
  ⟨height_adj_le G S R hab.symm, height_adj_le G S R hab⟩

/-- A height gap of at least two excludes an edge. -/
theorem not_adj_of_height_gap [Fintype V] (G : SimpleGraph V) (S : Finset V) (R : ℕ)
    {a b : V} (hgap : height G S R a + 1 < height G S R b) : ¬ G.Adj a b := by
  intro hab
  exact (Nat.not_lt_of_ge (height_adj_le G S R hab)) hgap

/-- A natural-valued function increasing by at most one along edges increases by
at most walk length.  This also applies to potentials on a replacement/cap graph. -/
theorem walk_potential_le (G : SimpleGraph V) (r : V → ℕ)
    (hstep : ∀ {a b}, G.Adj a b → r b ≤ r a + 1) {a b : V} (p : G.Walk a b) :
    r b ≤ r a + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hh := hstep h
    simp only [Walk.length_cons]
    omega

theorem height_le_add_length [Fintype V] (G : SimpleGraph V) (S : Finset V) (R : ℕ)
    {a b : V} (p : G.Walk a b) : height G S R b ≤ height G S R a + p.length :=
  walk_potential_le G (height G S R) (height_adj_le G S R) p

/-- Below the sentinel the minimum is attained by a root walk of exactly that
length, wholly inside the radius-`R` neighborhood. -/
theorem exists_root_walk_length_height [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (R : ℕ) {v : V} (hv : height G S R v ≤ R) :
    ∃ s ∈ S, ∃ p : (on G (near G S R)).Walk s v, p.length = height G S R v := by
  have hnear : v ∈ near G S (height G S R v) :=
    (height_le_iff_mem_near G S R hv v).1 (Nat.le_refl _)
  obtain ⟨s, hs, p, hp⟩ := (mem_near G S _ v).1 hnear
  have hmin : height G S R v ≤ p.length :=
    height_le_of_mem_near G S R ((mem_near G S _ v).2 ⟨s, hs, p, Nat.le_refl _⟩)
  refine ⟨s, hs, walkOn _ p (support_subset_near G S R hs p (hp.trans hv)), ?_⟩
  simpa using Nat.le_antisymm hp hmin

/- ## Pigeonhole clean bands -/

/-- A band of `w` consecutive natural-valued height layers, starting at `a`. -/
noncomputable def heightBand [Fintype V] (r : V → ℕ) (a w : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => a ≤ r v ∧ r v < a + w

@[simp] theorem mem_heightBand [Fintype V] (r : V → ℕ) (a w : ℕ) (v : V) :
    v ∈ heightBand r a w ↔ a ≤ r v ∧ r v < a + w := by
  classical
  simp [heightBand]

/-- Two equal-width consecutive bands can share a height only if their indices agree.
The zero-width case is harmless, since then both hypotheses are impossible. -/
private theorem band_index_unique {a w i j x : ℕ}
    (hi : a + w * i ≤ x ∧ x < a + w * i + w)
    (hj : a + w * j ≤ x ∧ x < a + w * j + w) : i = j := by
  have hij : i ≤ j := by
    by_contra hn
    have hm := Nat.mul_le_mul_left w (show j + 1 ≤ i by omega)
    simp only [Nat.mul_add, Nat.mul_one] at hm
    omega
  have hji : j ≤ i := by
    by_contra hn
    have hm := Nat.mul_le_mul_left w (show i + 1 ≤ j by omega)
    simp only [Nat.mul_add, Nat.mul_one] at hm
    omega
  exact Nat.le_antisymm hij hji

/-- Equal-width bands with different indices are disjoint. -/
theorem heightBand_disjoint [Fintype V] (r : V → ℕ) (a w : ℕ) {i j : ℕ}
    (hij : i ≠ j) :
    Disjoint (heightBand r (a + w * i) w) (heightBand r (a + w * j) w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hi hj
  exact hij (band_index_unique ((mem_heightBand _ _ _ _).1 hi)
    ((mem_heightBand _ _ _ _).1 hj))

/-- Among more consecutive bands than marked vertices, one band has no marked
vertex.  The height function is arbitrary, and the ambient type need not be finite. -/
theorem exists_clean_band (r : V → ℕ) (T : Finset V) (a w m : ℕ)
    (hT : T.card < m) :
    ∃ j < m, ∀ v ∈ T, ¬ (a + w * j ≤ r v ∧ r v < a + w * j + w) := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdirty : ∀ j : Fin m, ∃ v ∈ T,
      a + w * (j : ℕ) ≤ r v ∧ r v < a + w * (j : ℕ) + w :=
    fun j => hnone j j.isLt
  choose f hf hband using hdirty
  let fT : Fin m → T := fun j => ⟨f j, hf j⟩
  have hinj : Function.Injective fT := by
    intro i j heq
    have heq' : f i = f j := congrArg Subtype.val heq
    have hi := hband i
    rw [heq'] at hi
    exact Fin.ext (band_index_unique hi (hband j))
  have hcard := Fintype.card_le_of_injective fT hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- The finite-set formulation of `exists_clean_band`. -/
theorem exists_clean_band_disjoint [Fintype V] (r : V → ℕ) (T : Finset V)
    (a w m : ℕ) (hT : T.card < m) :
    ∃ j < m, Disjoint T (heightBand r (a + w * j) w) := by
  classical
  obtain ⟨j, hj, hclean⟩ := exists_clean_band r T a w m hT
  refine ⟨j, hj, Finset.disjoint_left.mpr ?_⟩
  intro v hvT hvB
  exact hclean v hvT ((mem_heightBand _ _ _ _).1 hvB)

/-- The `2 * B + 1` four-layer bands starting at `N + 1 + 4 * j` include a clean
one whenever the marked/error-endpoint set has at most `2 * B` vertices. -/
theorem exists_clean_four_band (r : V → ℕ) (T : Finset V) (N B : ℕ)
    (hT : T.card ≤ 2 * B) :
    ∃ j ≤ 2 * B, ∀ v ∈ T,
      r v < N + 1 + 4 * j ∨ N + 1 + 4 * j + 4 ≤ r v := by
  obtain ⟨j, hj, hclean⟩ := exists_clean_band r T (N + 1) 4 (2 * B + 1) (by omega)
  refine ⟨j, by omega, ?_⟩
  intro v hv
  have hh := hclean v hv
  omega

/-- A clean four-layer annulus beyond the controlled prefix `N`, with its last
layer at most `N + 4 * (2 * B + 1)`.  The sentinel can be used as an ordinary
height value; no distance-zero convention for disconnected vertices is involved. -/
theorem exists_clean_annulus (r : V → ℕ) (T : Finset V) (N B : ℕ)
    (hT : T.card ≤ 2 * B) :
    ∃ a, N < a ∧ a + 3 ≤ N + 4 * (2 * B + 1) ∧
      ∀ v ∈ T, r v < a ∨ a + 4 ≤ r v := by
  obtain ⟨j, hj, hclean⟩ := exists_clean_four_band r T N B hT
  exact ⟨N + 1 + 4 * j, by omega, by omega, hclean⟩

/-- A band whose highest layer is below the sentinel lies in the neighborhood. -/
theorem heightBand_subset_near [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R a w : ℕ) (hbound : a + w ≤ R + 1) :
    heightBand (height G S R) a w ⊆ near G S R := by
  intro v hv
  have hh := (mem_heightBand _ _ _ _).1 hv
  exact (height_le_iff_mem_near G S R (Nat.le_refl R) v).1 (by omega)

/-- A positive-height band is disjoint from the sources. -/
theorem heightBand_disjoint_sources [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R a w : ℕ) (ha : 0 < a) : Disjoint S (heightBand (height G S R) a w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvS hvB
  have hz := (height_eq_zero_iff G S R v).2 hvS
  have hh := (mem_heightBand _ _ _ _).1 hvB
  omega

/-- Packaged geometric form: the clean annulus lies in the chosen neighborhood,
starts strictly after `N`, and contains none of the marked/error endpoints. -/
theorem exists_clean_near_annulus [Fintype V] (G : SimpleGraph V) (S T : Finset V)
    (N B R : ℕ) (hT : T.card ≤ 2 * B) (hR : N + 4 * (2 * B + 1) ≤ R) :
    ∃ a, N < a ∧ a + 3 ≤ R ∧
      Disjoint T (heightBand (height G S R) a 4) ∧
      heightBand (height G S R) a 4 ⊆ near G S R := by
  classical
  obtain ⟨a, ha, hlast, hclean⟩ := exists_clean_annulus (height G S R) T N B hT
  refine ⟨a, ha, hlast.trans hR, ?_, heightBand_subset_near G S R a 4 (by omega)⟩
  apply Finset.disjoint_left.mpr
  intro v hvT hvB
  have hc := hclean v hvT
  have hb := (mem_heightBand _ _ _ _).1 hvB
  omega

end E74

/-
# A two-vertex profile cap

`capGraph G r a beta` retains the edges of `G` below height `a`, adds two
adjacent cap vertices, and redirects each edge into layer `a` to the cap
vertex indexed by its boundary `beta` bit.  Its vertex type is `V ⊕ Bool`:
original vertices of height at least `a` are retained as isolated vertices.

The small-profile argument uses a 1-Lipschitz potential and simple paths in
finite restrictions.  The four-color extension uses two disjoint two-color
palettes, so it does not require switching colors through the clean band.
-/

namespace E74

open SimpleGraph
universe u v
variable {V : Type u} {W : Type v}

/-- Two-vertex cap of the region strictly below height `a`. -/
def capGraph (G : SimpleGraph V) (r : V → ℕ) (a : ℕ) (beta : V → Bool) :
    SimpleGraph (V ⊕ Bool) where
  Adj
    | .inl x, .inl y => G.Adj x y ∧ r x < a ∧ r y < a
    | .inl x, .inr i => r x < a ∧ ∃ y, G.Adj x y ∧ r y = a ∧ beta y = i
    | .inr i, .inl y => r y < a ∧ ∃ x, G.Adj y x ∧ r x = a ∧ beta x = i
    | .inr i, .inr j => i ≠ j
  symm := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact ⟨h.1.symm, h.2.2, h.2.1⟩
      | inr j => exact h
    | inr i =>
      cases y with
      | inl y => exact h
      | inr j => exact h.symm
  loopless := by
    intro x h
    cases x with
    | inl x => exact G.loopless x h.1
    | inr i => exact h rfl

@[simp] theorem capGraph_adj_inl_inl (G : SimpleGraph V) (r : V → ℕ)
    (a : ℕ) (beta : V → Bool) (x y : V) :
    (capGraph G r a beta).Adj (.inl x) (.inl y) ↔
      G.Adj x y ∧ r x < a ∧ r y < a := Iff.rfl

@[simp] theorem capGraph_adj_inl_inr (G : SimpleGraph V) (r : V → ℕ)
    (a : ℕ) (beta : V → Bool) (x : V) (i : Bool) :
    (capGraph G r a beta).Adj (.inl x) (.inr i) ↔
      r x < a ∧ ∃ y, G.Adj x y ∧ r y = a ∧ beta y = i := Iff.rfl

@[simp] theorem capGraph_adj_inr_inl (G : SimpleGraph V) (r : V → ℕ)
    (a : ℕ) (beta : V → Bool) (i : Bool) (y : V) :
    (capGraph G r a beta).Adj (.inr i) (.inl y) ↔
      r y < a ∧ ∃ x, G.Adj y x ∧ r x = a ∧ beta x = i := Iff.rfl

@[simp] theorem capGraph_adj_inr_inr (G : SimpleGraph V) (r : V → ℕ)
    (a : ℕ) (beta : V → Bool) (i j : Bool) :
    (capGraph G r a beta).Adj (.inr i) (.inr j) ↔ i ≠ j := Iff.rfl

/-- The original bits, extended by bit `i` on cap vertex `i`. -/
def capBits (beta : V → Bool) : V ⊕ Bool → Bool := Sum.elim beta id

/-- A cap vertex has potential `a`; original potentials are truncated at `a`. -/
def capPotential (r : V → ℕ) (a : ℕ) : V ⊕ Bool → ℕ :=
  Sum.elim (fun x => min (r x) a) (fun _ => a)

/-- The cap potential is 1-Lipschitz whenever the original heights are. -/
theorem capPotential_adj (G : SimpleGraph V) (r : V → ℕ) (a : ℕ)
    (beta : V → Bool)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    {x y : V ⊕ Bool} (hxy : (capGraph G r a beta).Adj x y) :
    capPotential r a y ≤ capPotential r a x + 1 := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hh := hstep hxy.1
      simpa only [capPotential, Sum.elim_inl,
        Nat.min_eq_left (Nat.le_of_lt hxy.2.1),
        Nat.min_eq_left (Nat.le_of_lt hxy.2.2)] using hh
    | inr i =>
      obtain ⟨hx, y, hxy, hy, _⟩ := hxy
      have hh := hstep hxy
      simp only [capPotential, Sum.elim_inl, Sum.elim_inr,
        Nat.min_eq_left (Nat.le_of_lt hx)]
      omega
  | inr i =>
    cases y with
    | inl y =>
      have hy := hxy.1
      simp only [capPotential, Sum.elim_inl, Sum.elim_inr,
        Nat.min_eq_left (Nat.le_of_lt hy)]
      omega
    | inr j => simp [capPotential]

/-- Comparing monochromatic graphs after an injective relabeling compares
numbers of errors, even when the whole graphs have no such map. -/
private theorem cap_errors_card_le_of_map [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (beta : V → Bool) (c : W → Bool)
    (f : V ↪ W) (h : badGraph H c ≤ (badGraph G beta).map f) :
    (errors H c).card ≤ (errors G beta).card := by
  classical
  calc
    (errors H c).card ≤ ((errors G beta).map f.sym2Map).card := by
      apply Finset.card_le_card
      intro e he
      induction e using Sym2.inductionOn with
      | hf x y =>
        obtain ⟨x', y', hxy, rfl, rfl⟩ := h ((mem_errors H c x y).1 he)
        exact Finset.mem_map.mpr
          ⟨s(x', y'), (mem_errors G beta x' y').2 hxy, rfl⟩
    _ = (errors G beta).card := Finset.card_map _

section Geometry
variable [Fintype V]

/-- Below the cap boundary, the height test implies membership in the
neighborhood on which `beta` was chosen. -/
private theorem cap_mem_near (G : SimpleGraph V) (S : Finset V) (R a : ℕ)
    (haR : a ≤ R) {x : V} (hx : height G S R x ≤ a) : x ∈ near G S R :=
  (height_le_iff_mem_near G S R (Nat.le_refl R) x).1 (hx.trans haR)

/-- A boundary edge cannot have equal `beta` bits: its outer endpoint has
positive height and hence is not a source. -/
private theorem cap_boundary_bits_ne (G : SimpleGraph V) (S : Finset V)
    (R a : ℕ) (beta : V → Bool) (ha : 0 < a) (haR : a ≤ R)
    (hinside : ∀ x y, (on G (near G S R)).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S)
    {x y : V} (hxy : G.Adj x y) (hx : height G S R x < a)
    (hy : height G S R y = a) : beta x ≠ beta y := by
  intro heq
  have hyS := (hinside x y ⟨hxy,
    cap_mem_near G S R a haR (Nat.le_of_lt hx),
    cap_mem_near G S R a haR (Nat.le_of_eq hy)⟩ heq).2
  have hz := (height_eq_zero_iff G S R y).2 hyS
  omega

/-- All errors of the cap's distinguished cut are mapped from `G[S]`. -/
theorem cap_badGraph_le (G : SimpleGraph V) (S : Finset V) (R a : ℕ)
    (beta : V → Bool) (ha : 0 < a) (haR : a ≤ R)
    (hinside : ∀ x y, (on G (near G S R)).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S) :
    badGraph (capGraph G (height G S R) a beta) (capBits beta) ≤
      (badGraph (on G S) beta).map Function.Embedding.inl := by
  intro x y h
  rcases h with ⟨hxy, heq⟩
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hcol : beta x = beta y := heq
      have hS := hinside x y ⟨hxy.1,
        cap_mem_near G S R a haR (Nat.le_of_lt hxy.2.1),
        cap_mem_near G S R a haR (Nat.le_of_lt hxy.2.2)⟩ hcol
      exact ⟨x, y, ⟨⟨hxy.1, hS⟩, hcol⟩, rfl, rfl⟩
    | inr i =>
      obtain ⟨hx, y, hxy, hy, hbi⟩ := hxy
      exact (cap_boundary_bits_ne G S R a beta ha haR hinside hxy hx hy
        (show beta x = beta y from heq.trans hbi.symm)).elim
  | inr i =>
    cases y with
    | inl y =>
      obtain ⟨hy, x, hyx, hx, hbi⟩ := hxy
      exact (cap_boundary_bits_ne G S R a beta ha haR hinside hyx hy hx
        (show beta y = beta x from heq.symm.trans hbi.symm)).elim
    | inr j => exact (hxy heq).elim

/-- Capping preserves the exact defect of the source set.  No bound on the
cardinality of the source set is needed. -/
theorem cap_defect (G : SimpleGraph V) (S : Finset V) (R a : ℕ)
    (beta : V → Bool) (ha : 0 < a) (haR : a ≤ R)
    (hbeta : (errors (on G (near G S R)) beta).card = defect (on G S))
    (hinside : ∀ x y, (on G (near G S R)).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S) :
    defect (capGraph G (height G S R) a beta) = defect (on G S) := by
  classical
  apply Nat.le_antisymm
  · calc
      defect (capGraph G (height G S R) a beta) ≤
          (errors (capGraph G (height G S R) a beta) (capBits beta)).card :=
        defect_le_errors _ _
      _ ≤ (errors (on G S) beta).card :=
        cap_errors_card_le_of_map _ _ _ _ Function.Embedding.inl
          (cap_badGraph_le G S R a beta ha haR hinside)
      _ ≤ (errors (on G (near G S R)) beta).card :=
        Finset.card_le_card (errors_on_mono G (subset_near G S R) beta)
      _ = defect (on G S) := hbeta
  · let f : on G S →g capGraph G (height G S R) a beta :=
      { toFun := Sum.inl
        map_rel' := by
          intro x y hxy
          have hx := (height_eq_zero_iff G S R x).2 hxy.2.1
          have hy := (height_eq_zero_iff G S R y).2 hxy.2.2
          exact ⟨hxy.1, by omega, by omega⟩ }
    exact defect_mono_of_injective f Sum.inl_injective

end Geometry

/- ## Simple-path separation and small profiles -/

/-- A walk of a finite restriction starting inside the restriction stays in it. -/
private theorem cap_on_walk_support (G : SimpleGraph W) (U : Finset W)
    {x y : W} (p : (on G U).Walk x y) :
    x ∈ U → ∀ z ∈ p.support, z ∈ U := by
  induction p with
  | nil =>
    intro hx z hz
    simpa using (show z = _ from by simpa using hz) ▸ hx
  | cons h p ih =>
    intro hx z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih h.2.2 z hz

/-- A simple path in a finite restriction has fewer edges than there are
vertices in the restricting set, rather than merely in the ambient type. -/
private theorem cap_on_path_length_lt (G : SimpleGraph W) (U : Finset W)
    {x y : W} (p : (on G U).Walk x y) (hp : p.IsPath) (hx : x ∈ U) :
    p.length < U.card := by
  classical
  have hs : p.support.toFinset ⊆ U := by
    intro z hz
    exact cap_on_walk_support G U p hx z (List.mem_toFinset.mp hz)
  have hlen : p.length + 1 ≤ U.card := by
    calc
      p.length + 1 = p.support.length := p.length_support.symm
      _ = p.support.toFinset.card := (List.toFinset_card_of_nodup hp.support_nodup).symm
      _ ≤ U.card := Finset.card_le_card hs
  omega

/-- Whether the component of `x` in the finite restriction meets a cap vertex.
Isolated cap vertices are included, even when outside `U`; this is harmless
and ensures that every cap vertex uses its distinguished bit. -/
def capReaches (G : SimpleGraph V) (r : V → ℕ) (a : ℕ) (beta : V → Bool)
    (U : Finset (V ⊕ Bool)) (x : V ⊕ Bool) : Prop :=
  ∃ i : Bool, (on (capGraph G r a beta) U).Reachable x (.inr i)

private theorem capReaches_adj (G : SimpleGraph V) (r : V → ℕ) (a : ℕ)
    (beta : V → Bool) (U : Finset (V ⊕ Bool)) {x y : V ⊕ Bool}
    (hxy : (on (capGraph G r a beta) U).Adj x y) :
    capReaches G r a beta U x ↔ capReaches G r a beta U y := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hxy.reachable.symm.trans hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hxy.reachable.trans hi⟩

/-- In fewer than `a` vertices, a cap-reaching component cannot meet
potential zero.  This remains valid for isolated originals and empty sets. -/
theorem capReaches_not_zero (G : SimpleGraph V) (r : V → ℕ) (a : ℕ)
    (beta : V → Bool) (U : Finset (V ⊕ Bool))
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (hU : U.card < a) {x : V} (hx : r x = 0) (hxU : Sum.inl x ∈ U) :
    ¬ capReaches G r a beta U (.inl x) := by
  rintro ⟨i, hi⟩
  obtain ⟨p, hp⟩ := hi.exists_isPath
  have hlen := cap_on_path_length_lt _ U p hp hxU
  have hpot := walk_potential_le (on (capGraph G r a beta) U)
    (capPotential r a) (fun {_ _} h => capPotential_adj G r a beta hstep h.1) p
  simp only [capPotential, Sum.elim_inl, Sum.elim_inr, hx, Nat.zero_min,
    Nat.zero_add] at hpot
  omega

/-- Abstract small-profile cap lemma.  The only hypotheses are a 1-Lipschitz
height function, sources of height zero, and concentration of the distinguished
cut's errors in the mapped source graph. -/
theorem capGraph_profile_le [Fintype V] (G : SimpleGraph V) (r : V → ℕ)
    (a : ℕ) (beta : V → Bool) (S : Finset V)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (hS : ∀ x ∈ S, r x = 0)
    (hbad : badGraph (capGraph G r a beta) (capBits beta) ≤
      (badGraph (on G S) beta).map Function.Embedding.inl)
    {n : ℕ} (hn : n < a) :
    profile (capGraph G r a beta) n ≤ profile G n := by
  classical
  apply (profile_le_iff _ n _).2
  intro U hUn
  let s : Finset V := U.preimage Sum.inl Sum.inl_injective.injOn
  have hs : s.card ≤ n := by
    calc
      s.card ≤ U.card := by
        dsimp [s]
        rw [Finset.card_preimage]
        exact Finset.card_filter_le _ _
      _ ≤ n := hUn
  obtain ⟨c, hc⟩ := exists_optimal (on G s)
  let d : V ⊕ Bool → Bool := fun x =>
    if capReaches G r a beta U x then capBits beta x else Sum.elim c id x
  have hmap : badGraph (on (capGraph G r a beta) U) d ≤
      (badGraph (on G s) c).map Function.Embedding.inl := by
    intro x y h
    rcases h with ⟨hxy, heq⟩
    have hreach := capReaches_adj G r a beta U hxy
    by_cases hx : capReaches G r a beta U x
    · have hy := hreach.mp hx
      have hbits : capBits beta x = capBits beta y := by simpa [d, hx, hy] using heq
      obtain ⟨u, v, huv, rfl, rfl⟩ := hbad ⟨hxy.1, hbits⟩
      exact (capReaches_not_zero G r a beta U hstep (hUn.trans_lt hn)
        (hS u huv.1.2.1) hxy.2.1 hx).elim
    · have hy : ¬ capReaches G r a beta U y := fun hy => hx (hreach.mpr hy)
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          refine ⟨x, y, ⟨⟨hxy.1.1, Finset.mem_preimage.mpr hxy.2.1,
            Finset.mem_preimage.mpr hxy.2.2⟩, ?_⟩, rfl, rfl⟩
          simpa [d, hx, hy] using heq
        | inr i => exact (hy ⟨i, .rfl⟩).elim
      | inr i => exact (hx ⟨i, .rfl⟩).elim
  calc
    defect (on (capGraph G r a beta) U) ≤ (errors _ d).card := defect_le_errors _ d
    _ ≤ (errors (on G s) c).card :=
      cap_errors_card_le_of_map _ _ _ _ Function.Embedding.inl hmap
    _ = defect (on G s) := hc
    _ ≤ profile G n := defect_on_le_profile G hs

/-- Every profile coordinate strictly before the cap height is controlled. -/
theorem cap_profile_le [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R a : ℕ) (beta : V → Bool) (haR : a ≤ R)
    (hinside : ∀ x y, (on G (near G S R)).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S)
    {n : ℕ} (hn : n < a) :
    profile (capGraph G (height G S R) a beta) n ≤ profile G n :=
  capGraph_profile_le G (height G S R) a beta S (height_adj_le G S R)
    (fun x hx => (height_eq_zero_iff G S R x).2 hx)
    (cap_badGraph_le G S R a beta (by omega) haR hinside) hn

/- ## Four-color extension using disjoint palettes -/

/-- Two distinct colors in `Fin 4` have a disjoint pair of remaining colors.
This is a closed finite proposition, checked by the kernel's `decide`. -/
private theorem cap_four_palette :
    ∀ A : Bool → Fin 4, A false ≠ A true →
      ∃ B : Bool → Fin 4, B false ≠ B true ∧ ∀ i j, A i ≠ B j := by
  decide

private theorem cap_bool_injective {α : Type*} (f : Bool → α)
    (hf : f false ≠ f true) : Function.Injective f := by
  intro i j hij
  cases i <;> cases j <;> simp_all

/-- Every four-coloring of the abstract cap extends to the original graph,
agreeing with it below height `a`.  The layer `a` uses the cap palette `A`,
ordinary outer vertices use its disjoint complement `B`, and outer error
endpoints use `A` with an independent proper binary coloring.

Only the boundary layer needs to be proper under `beta`.  The four-layer
clean band separates the outer error endpoints from the boundary. -/
theorem capGraph_coloring_extends [Fintype V] (G : SimpleGraph V)
    (r : V → ℕ) (a : ℕ) (beta sigma : V → Bool) (T : Finset V)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (hproper : ∀ {x y}, G.Adj x y → r x = a → r y = a → beta x ≠ beta y)
    (hcover : ∀ x y, G.Adj x y → sigma x = sigma y → x ∈ T ∧ y ∈ T)
    (hclean : ∀ x ∈ T, r x < a ∨ a + 4 ≤ r x)
    (hout : defect (on G (T.filter (fun x => a + 4 ≤ r x))) = 0)
    (c : (capGraph G r a beta).Coloring (Fin 4)) :
    ∃ d : G.Coloring (Fin 4), ∀ x, r x < a → d x = c (.inl x) := by
  classical
  let O := T.filter (fun x => a + 4 ≤ r x)
  obtain ⟨tau, htau⟩ := (defect_zero_iff (on G O)).1 hout
  let A : Bool → Fin 4 := fun i => c (.inr i)
  have hAft : A false ≠ A true := c.valid (by simp)
  have hA : Function.Injective A := cap_bool_injective A hAft
  obtain ⟨B, hBft, hAB⟩ := cap_four_palette A hAft
  have hB : Function.Injective B := cap_bool_injective B hBft
  let d : V → Fin 4 := fun x =>
    if r x < a then c (.inl x)
    else if r x = a then A (beta x)
    else if x ∈ O then A (tau x)
    else B (sigma x)
  have hd : ∀ {x y}, G.Adj x y → r x ≤ r y → d x ≠ d y := by
    intro x y hxy hle heq
    have hstepxy := hstep hxy
    by_cases hx : r x < a
    · by_cases hy : r y < a
      · exact c.valid (show (capGraph G r a beta).Adj (.inl x) (.inl y) from
          ⟨hxy, hx, hy⟩) (by simpa [d, hx, hy] using heq)
      · have hya : r y = a := by omega
        exact c.valid (show (capGraph G r a beta).Adj (.inl x) (.inr (beta y)) from
          ⟨hx, y, hxy, hya, rfl⟩) (by simpa [d, hx, hy, hya, A] using heq)
    · by_cases hxa : r x = a
      · by_cases hya : r y = a
        · have hy : ¬ r y < a := by omega
          exact hproper hxy hxa hya
            (hA (by simpa [d, hx, hy, hxa, hya] using heq))
        · have hy : ¬ r y < a := by omega
          have hyO : y ∉ O := by
            intro hyO
            have houter := (Finset.mem_filter.mp hyO).2
            omega
          exact hAB (beta x) (sigma y)
            (by simpa [d, hx, hy, hxa, hya, hyO] using heq)
      · have hy : ¬ r y < a := by omega
        have hya : r y ≠ a := by omega
        by_cases hxO : x ∈ O
        · by_cases hyO : y ∈ O
          · exact htau ⟨hxy, hxO, hyO⟩
              (hA (by simpa [d, hx, hy, hxa, hya, hxO, hyO] using heq))
          · exact hAB (tau x) (sigma y)
              (by simpa [d, hx, hy, hxa, hya, hxO, hyO] using heq)
        · by_cases hyO : y ∈ O
          · exact hAB (tau y) (sigma x)
              (by simpa [d, hx, hy, hxa, hya, hxO, hyO] using heq.symm)
          · have hcol : sigma x = sigma y :=
              hB (by simpa [d, hx, hy, hxa, hya, hxO, hyO] using heq)
            have hxT := (hcover x y hxy hcol).1
            have houter : a + 4 ≤ r x := by
              have hh := hclean x hxT
              omega
            exact hxO (Finset.mem_filter.mpr ⟨hxT, houter⟩)
  let dc : G.Coloring (Fin 4) := SimpleGraph.Coloring.mk d (by
    intro x y hxy
    rcases le_total (r x) (r y) with hle | hle
    · exact hd hxy hle
    · exact (hd hxy.symm hle).symm)
  refine ⟨dc, ?_⟩
  intro x hx
  change d x = c (.inl x)
  simp [d, hx]

/-- Four-colorability of the geometric cap implies four-colorability of `G`.
The safe sentinel in `height` means this also colors components disjoint from
`S`, with no connectivity assumption. -/
theorem cap_colorable_four [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (R a : ℕ) (beta sigma : V → Bool) (T : Finset V)
    (ha : 0 < a) (haR : a ≤ R)
    (hinside : ∀ x y, (on G (near G S R)).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S)
    (hcover : ∀ x y, G.Adj x y → sigma x = sigma y → x ∈ T ∧ y ∈ T)
    (hclean : ∀ x ∈ T, height G S R x < a ∨ a + 4 ≤ height G S R x)
    (hout : defect (on G (T.filter (fun x => a + 4 ≤ height G S R x))) = 0) :
    (capGraph G (height G S R) a beta).Colorable 4 → G.Colorable 4 := by
  rintro ⟨c⟩
  have hproper : ∀ {x y}, G.Adj x y → height G S R x = a →
      height G S R y = a → beta x ≠ beta y := by
    intro x y hxy hx hy heq
    have hxS := (hinside x y ⟨hxy,
      cap_mem_near G S R a haR (Nat.le_of_eq hx),
      cap_mem_near G S R a haR (Nat.le_of_eq hy)⟩ heq).1
    have hz := (height_eq_zero_iff G S R x).2 hxS
    omega
  obtain ⟨d, _⟩ := capGraph_coloring_extends G (height G S R) a beta sigma T
    (height_adj_le G S R) hproper hcover hclean hout c
  exact ⟨d⟩

/-- The requested finite cap: exact source defect, no increase in any profile
coordinate through `N`, and a four-color extension back to `G`.

The returned graph is explicitly `capGraph G (height G S R) a beta` on
`V ⊕ Bool`.  No hypothesis on `S.card` (or nonemptiness of any set) is used.
The component results above only need `a ≤ R`; this wrapper retains the
four-layer-band interface `a + 3 ≤ R` for the plateau theorem. -/
theorem exists_cap [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (N R a : ℕ) (beta sigma : V → Bool) (T : Finset V)
    (hNa : N < a) (haR : a + 3 ≤ R)
    (hbeta : (errors (on G (near G S R)) beta).card = defect (on G S))
    (hinside : ∀ x y, (on G (near G S R)).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S)
    (hcover : ∀ x y, G.Adj x y → sigma x = sigma y → x ∈ T ∧ y ∈ T)
    (hclean : ∀ x ∈ T, height G S R x < a ∨ a + 4 ≤ height G S R x)
    (hout : defect (on G (T.filter (fun x => a + 4 ≤ height G S R x))) = 0) :
    ∃ C : SimpleGraph (V ⊕ Bool),
      defect C = defect (on G S) ∧
      (∀ n, n ≤ N → profile C n ≤ profile G n) ∧
      (C.Colorable 4 → G.Colorable 4) := by
  refine ⟨capGraph G (height G S R) a beta,
    cap_defect G S R a beta (by omega) (by omega) hbeta hinside, ?_,
    cap_colorable_four G S R a beta sigma T (by omega) (by omega)
      hinside hcover hclean hout⟩
  intro n hn
  exact cap_profile_le G S R a beta (by omega) hinside (hn.trans_lt hNa)

end E74

/-
# An abstract profile staircase

A family of bounded, nondecreasing natural-number profiles is excluded by a
single nondecreasing divergent envelope, provided it has uniform positive-value
detection and uniform plateau-to-cap replacement.  No graph definitions are used.

The thresholds use an unoptimized recursion: at stage `B`, start at the maximum
of the preceding threshold and the detection index, iterate the plateau modulus
`B` times, and put the new threshold one beyond the last sample.
-/

set_option maxHeartbeats 800000

namespace E74

open Filter

/-- Repeated application of a plateau modulus, with the profile bound fixed. -/
def profileSample (M : ℕ → ℕ → ℕ) (B start : ℕ) : ℕ → ℕ
  | 0 => start
  | s + 1 => M B (profileSample M B start s)

/-- Inflationary plateau moduli give nondecreasing sample indices. -/
theorem profileSample_monotone (M : ℕ → ℕ → ℕ)
    (hM : ∀ B N, N ≤ M B N) (B start : ℕ) :
    Monotone (profileSample M B start) := by
  apply monotone_nat_of_le_succ
  intro s
  exact hM B (profileSample M B start s)

/-- The unoptimized recursive thresholds.  In the successor case there are
`B + 1` samples, indexed from `0` through `B`, where `B = j + 1`. -/
def profileThreshold (M : ℕ → ℕ → ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      profileSample M (j + 1) (max (profileThreshold M d j) (d (j + 1))) (j + 1) + 1

/-- Each new threshold is strictly larger than its predecessor. -/
theorem profileThreshold_strictMono (M : ℕ → ℕ → ℕ) (d : ℕ → ℕ)
    (hM : ∀ B N, N ≤ M B N) : StrictMono (profileThreshold M d) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hstart := le_max_left (profileThreshold M d j) (d (j + 1))
  have hs : max (profileThreshold M d j) (d (j + 1)) ≤
      profileSample M (j + 1) (max (profileThreshold M d j) (d (j + 1))) (j + 1) :=
    profileSample_monotone M hM (j + 1)
      (max (profileThreshold M d j) (d (j + 1))) (Nat.zero_le (j + 1))
  rw [profileThreshold]
  omega

/-- The inverse staircase: its value is the first `j` for which `n` lies
strictly before threshold `j + 1`. -/
def staircase (T : ℕ → ℕ) (hT : StrictMono T) (n : ℕ) : ℕ :=
  Nat.find (show ∃ j, n < T (j + 1) from
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (hT.id_le (n + 1))⟩)

/-- Every index lies strictly before the threshold following its staircase value. -/
theorem staircase_lt_next (T : ℕ → ℕ) (hT : StrictMono T) (n : ℕ) :
    n < T (staircase T hT n + 1) := by
  exact Nat.find_spec (p := fun j => n < T (j + 1)) _

/-- Before threshold `j + 1` the staircase is at most `j`. -/
theorem staircase_le_of_lt (T : ℕ → ℕ) (hT : StrictMono T) {n j : ℕ}
    (hn : n < T (j + 1)) : staircase T hT n ≤ j := by
  exact Nat.find_min' _ hn

/-- At and after threshold `j` the staircase is at least `j`. -/
theorem le_staircase_of_le (T : ℕ → ℕ) (hT : StrictMono T) {n j : ℕ}
    (hn : T j ≤ n) : j ≤ staircase T hT n := by
  by_contra h
  have hindex : staircase T hT n + 1 ≤ j := by omega
  have hnext := hT.monotone hindex
  have hspec := staircase_lt_next T hT n
  omega

/-- The inverse staircase is nondecreasing. -/
theorem staircase_monotone (T : ℕ → ℕ) (hT : StrictMono T) :
    Monotone (staircase T hT) := by
  intro n m hnm
  exact staircase_le_of_lt T hT (lt_of_le_of_lt hnm (staircase_lt_next T hT m))

/-- The inverse staircase genuinely tends to infinity. -/
theorem staircase_tendsto (T : ℕ → ℕ) (hT : StrictMono T) :
    Tendsto (staircase T hT) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro j
  exact ⟨T j, fun n hn => le_staircase_of_le T hT hn⟩

/-- A positive nondecreasing sequence cannot strictly increase `B` times
while its last value remains at most `B`. -/
theorem exists_adjacent_plateau (a : ℕ → ℕ) (ha : Monotone a) (B : ℕ)
    (hpos : 0 < a 0) (hbound : a B ≤ B) :
    ∃ s < B, a s = a (s + 1) := by
  by_contra h
  have hstrict : ∀ s < B, a s < a (s + 1) := by
    intro s hs
    have hle : a s ≤ a (s + 1) := ha (Nat.le_succ s)
    have hne : a s ≠ a (s + 1) := fun heq => h ⟨s, hs, heq⟩
    omega
  have hlower : ∀ s, s ≤ B → a 0 + s ≤ a s := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        intro hs
        have hi := ih (by omega)
        have hstep := hstrict s (by omega)
        omega
  have hlast := hlower B le_rfl
  omega

/--
Concrete-modulus form of the abstract profile theorem.

`d B` detects a positive value in every member bounded by `B`.  `M B N ≥ N`
is a uniform plateau endpoint: equality of the values at `N` and `M B N`,
when positive, gives another member bounded pointwise by `min (p n) (p N)`.
No monotonicity of either modulus is assumed.
-/
theorem exists_avoiding_staircase_of_moduli
    (P : Set (ℕ → ℕ)) (d : ℕ → ℕ) (M : ℕ → ℕ → ℕ)
    (hmono : ∀ p ∈ P, Monotone p)
    (hbounded : ∀ p ∈ P, ∃ B, ∀ n, p n ≤ B)
    (hM : ∀ B N, N ≤ M B N)
    (hcap : ∀ B N p, p ∈ P → (∀ n, p n ≤ B) →
      p N = p (M B N) → 0 < p N →
      ∃ q ∈ P, ∀ n, q n ≤ min (p n) (p N))
    (hpositive : ∀ B p, p ∈ P → (∀ n, p n ≤ B) → 0 < p (d B)) :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      ∀ p ∈ P, ¬ (∀ n, p n ≤ f n) := by
  let T := profileThreshold M d
  have hT : StrictMono T := profileThreshold_strictMono M d hM
  let f := staircase T hT
  have hgood : ∀ j, ∀ p ∈ P, ¬ (∀ n, p n ≤ min (f n) j) := by
    intro j
    induction j with
    | zero =>
        intro p hp hpf
        have hpzero : ∀ n, p n ≤ 0 := fun n => (hpf n).trans (min_le_right _ _)
        have hpos := hpositive 0 p hp hpzero
        have hz := hpzero (d 0)
        omega
    | succ j ih =>
        intro p hp hpf
        have hpB : ∀ n, p n ≤ j + 1 := fun n => (hpf n).trans (min_le_right _ _)
        have hpf' : ∀ n, p n ≤ f n := fun n => (hpf n).trans (min_le_left _ _)
        let start := max (T j) (d (j + 1))
        let a := profileSample M (j + 1) start
        have ha : Monotone a := profileSample_monotone M hM (j + 1) start
        have hbefore : ∀ s ≤ j + 1, a s < T (j + 1) := by
          intro s hs
          have hle := ha hs
          change a s < a (j + 1) + 1
          omega
        have hsmall : ∀ s ≤ j + 1, p (a s) ≤ j := by
          intro s hs
          exact (hpf' (a s)).trans (staircase_le_of_lt T hT (hbefore s hs))
        have hdetect : d (j + 1) ≤ a 0 := le_max_right _ _
        have hpos : 0 < p (a 0) :=
          lt_of_lt_of_le (hpositive (j + 1) p hp hpB) (hmono p hp hdetect)
        obtain ⟨s, hs, heq⟩ := exists_adjacent_plateau (fun s => p (a s))
          ((hmono p hp).comp ha) (j + 1) hpos
          ((hsmall (j + 1) le_rfl).trans (Nat.le_succ j))
        have hpos_s : 0 < p (a s) :=
          lt_of_lt_of_le hpos (hmono p hp (ha (Nat.zero_le s)))
        have heq' : p (a s) = p (M (j + 1) (a s)) := heq
        obtain ⟨q, hq, hqcap⟩ := hcap (j + 1) (a s) p hp hpB heq' hpos_s
        apply ih q hq
        intro n
        apply le_min
        · exact ((hqcap n).trans (min_le_left _ _)).trans (hpf' n)
        · exact ((hqcap n).trans (min_le_right _ _)).trans (hsmall s hs.le)
  refine ⟨f, staircase_monotone T hT, staircase_tendsto T hT, ?_⟩
  intro p hp hpf
  obtain ⟨B, hpB⟩ := hbounded p hp
  exact hgood B p hp (fun n => le_min (hpf n) (hpB n))

/--
Abstract family-of-profiles lemma.  The only assumptions are:

* every member is nondecreasing and bounded;
* for each bound and starting index there is a uniform later plateau endpoint
  that permits pointwise capping while staying in the family;
* for each bound there is a uniform index detecting positivity.

Then some nondecreasing divergent natural-number envelope dominates no member.
-/
theorem exists_avoiding_staircase
    (P : Set (ℕ → ℕ))
    (hmono : ∀ p ∈ P, Monotone p)
    (hbounded : ∀ p ∈ P, ∃ B, ∀ n, p n ≤ B)
    (hcap : ∀ B N, ∃ M, N ≤ M ∧
      ∀ p ∈ P, (∀ n, p n ≤ B) → p N = p M → 0 < p N →
        ∃ q ∈ P, ∀ n, q n ≤ min (p n) (p N))
    (hpositive : ∀ B, ∃ d, ∀ p ∈ P, (∀ n, p n ≤ B) → 0 < p d) :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      ∀ p ∈ P, ¬ (∀ n, p n ≤ f n) := by
  classical
  choose d hd using hpositive
  choose M hM hMc using hcap
  exact exists_avoiding_staircase_of_moduli P d M hmono hbounded hM hMc hd

end E74

/-
# Uniform plateau reduction

A bounded binary defect and a sufficiently long plateau in its local profile
permit replacement by a graph of the plateau's defect.  The replacement does
not increase the profile and preserves failure of four-colorability.
-/

namespace E74

open SimpleGraph
universe u
variable {V : Type u}

/-- Radius leaving room for more clean bands than there are error endpoints. -/
def plateauRadius (B N : ℕ) : ℕ := N + 4 * (2 * B + 1)

/-- A diameter bound for the neighborhood of a source set of size at most `N`. -/
def plateauDiameter (B N : ℕ) : ℕ := N * (2 * plateauRadius B N + 1)

/-- The plateau endpoint includes all possible local-defect witness bounds. -/
def plateauBound (B N : ℕ) : ℕ :=
  max (N + 2 * B) ((Finset.range (B + 1)).sup (witnessBound (plateauDiameter B N)))

theorem le_plateauBound (B N : ℕ) : N ≤ plateauBound B N :=
  (Nat.le_add_right N (2 * B)).trans (le_max_left _ _)

theorem witnessBound_le_plateauBound (B N t : ℕ) (ht : t ≤ B) :
    witnessBound (plateauDiameter B N) t ≤ plateauBound B N := by
  apply le_trans _ (le_max_right _ _)
  exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

/-- The neighborhood of a set attaining the plateau is itself saturated. -/
theorem defect_near_eq_of_plateau [Fintype V] (G : SimpleGraph V) (B N : ℕ)
    (hB : defect G ≤ B)
    (hplateau : profile G N = profile G (plateauBound B N))
    (S : Finset V) (hS : S.card ≤ N) (hSdef : defect (on G S) = profile G N) :
    defect (on G (near G S (plateauRadius B N))) = profile G N := by
  classical
  apply Nat.le_antisymm
  · by_contra h
    have hlt : profile G N < defect (on G (near G S (plateauRadius B N))) :=
      Nat.lt_of_not_ge h
    obtain ⟨s, hs, hdef⟩ := exists_bounded_diameter_witness
      (on G (near G S (plateauRadius B N))) (plateauDiameter B N) (profile G N)
      (near_component_diameter_le G S (plateauRadius B N) N hS) hlt
    have hsM : s.card ≤ plateauBound B N :=
      hs.trans (witnessBound_le_plateauBound B N (profile G N)
        ((profile_le_defect G N).trans hB))
    have hlocal : defect (on (on G (near G S (plateauRadius B N))) s) ≤
        profile G (plateauBound B N) :=
      (defect_mono (on_mono (on_le G _) s)).trans (defect_on_le_profile G hsM)
    rw [← hplateau] at hlocal
    exact (Nat.not_lt_of_ge hlocal) hdef
  · rw [← hSdef]
    exact defect_on_mono G (subset_near G S (plateauRadius B N))

/-- A finite plateau permits a profile-dominated, lower-defect replacement.
The replacement graph need not be an actual subgraph of `G`. -/
theorem plateau_replacement [Fintype V] (G : SimpleGraph V) (B N : ℕ)
    (hB : defect G ≤ B)
    (hplateau : profile G N = profile G (plateauBound B N)) :
    ∃ C : SimpleGraph (V ⊕ Bool),
      defect C = profile G N ∧
      (∀ n, profile C n ≤ min (profile G n) (profile G N)) ∧
      (C.Colorable 4 → G.Colorable 4) := by
  classical
  obtain ⟨S, hS, hSdef⟩ := exists_profile_set G N
  have hnear := defect_near_eq_of_plateau G B N hB hplateau S hS hSdef
  obtain ⟨beta, hbeta⟩ := exists_optimal (on G (near G S (plateauRadius B N)))
  have hinside : ∀ x y, (on G (near G S (plateauRadius B N))).Adj x y →
      beta x = beta y → x ∈ S ∧ y ∈ S := by
    intro x y hxy hcol
    exact optimal_errors_inside G (subset_near G S (plateauRadius B N))
      (hSdef.trans hnear.symm) hbeta hxy hcol
  obtain ⟨sigma, T, hsigma, hT, hcover⟩ := exists_optimal_endpoints G
  have hTB : T.card ≤ 2 * B := hT.trans (Nat.mul_le_mul_left 2 hB)
  obtain ⟨a, hNa, haR, hclean⟩ :=
    exists_clean_annulus (height G S (plateauRadius B N)) T N B hTB
  let Tout := T.filter (fun x => a + 4 ≤ height G S (plateauRadius B N) x)
  have hdisj : Disjoint S Tout := by
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hz := (height_eq_zero_iff G S (plateauRadius B N) x).mpr hx
    have hh := (Finset.mem_filter.mp hxt).2
    omega
  have hTout : Tout.card ≤ 2 * B := (Finset.card_filter_le _ _).trans hTB
  have hcard : (S ∪ Tout).card ≤ plateauBound B N := by
    apply (Finset.card_union_le S Tout).trans
    exact (Nat.add_le_add hS hTout).trans (le_max_left _ _)
  have hout : defect (on G Tout) = 0 := by
    have hsum := (defect_on_union_ge G hdisj).trans (defect_on_le_profile G hcard)
    rw [hSdef, ← hplateau] at hsum
    omega
  obtain ⟨C, hCdef, hCprofile, hextend⟩ :=
    exists_cap G S N (plateauRadius B N) a beta sigma T hNa haR
      (hbeta.trans (hnear.trans hSdef.symm)) hinside
      (fun x y hxy hcol => hcover hxy hcol) hclean hout
  have hC : defect C = profile G N := hCdef.trans hSdef
  refine ⟨C, hC, ?_, hextend⟩
  intro n
  have hCt : profile C n ≤ profile G N := (profile_le_defect C n).trans_eq hC
  refine le_min ?_ hCt
  by_cases hn : n ≤ N
  · exact hCprofile n hn
  · exact hCt.trans (profile_monotone G (by omega))

end E74

/-
# From the finite profile envelope to the Spec envelope

The Spec supremum is over all finite subgraphs of exactly `n` vertices.
We first identify its deletion distance with the binary-cut defect and prove
that this supremum is bounded.  Restrictions used in the internal profile
are then realized with their actual vertex sets (not with isolated vertices
counted), before applying finite-subgraph compactness.
-/

namespace E74

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Finite vertex sets give finite edge sets, even in an infinite ambient graph. -/
theorem subgraph_edgeSet_finite (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.Finite := by
  classical
  letI : Fintype A.verts := hA.fintype
  rw [← A.image_coe_edgeSet_coe]
  exact (Set.toFinite A.coe.edgeSet).image _

/-- The ambient edges on which a binary assignment to a subgraph agrees. -/
noncomputable def subgraphCutEdges (A : G.Subgraph) [Fintype A.verts]
    (c : A.verts → Bool) : Set (Sym2 V) :=
  Sym2.map (Subtype.val : A.verts → V) '' (errors A.coe c : Set (Sym2 A.verts))

theorem subgraphCutEdges_subset (A : G.Subgraph) [Fintype A.verts]
    (c : A.verts → Bool) : subgraphCutEdges A c ⊆ A.edgeSet := by
  rintro _ ⟨e, he, rfl⟩
  induction e using Sym2.inductionOn with
  | hf x y =>
    exact ((mem_errors A.coe c x y).mp he).1

@[simp] theorem subgraphCutEdges_ncard (A : G.Subgraph) [Fintype A.verts]
    (c : A.verts → Bool) : (subgraphCutEdges A c).ncard = (errors A.coe c).card := by
  classical
  rw [subgraphCutEdges, Set.ncard_image_of_injective _
    (Sym2.map.injective Subtype.val_injective)]
  exact Set.ncard_coe_finset _

/-- Deleting precisely the monochromatic edges leaves a bipartite graph. -/
theorem subgraph_delete_cutEdges_bipartite (A : G.Subgraph) [Fintype A.verts]
    (c : A.verts → Bool) : (A.deleteEdges (subgraphCutEdges A c)).coe.IsBipartite := by
  let C : (A.deleteEdges (subgraphCutEdges A c)).coe.Coloring Bool :=
    SimpleGraph.Coloring.mk c (by
      intro x y hxy hcol
      exact hxy.2 ⟨s(x, y), (mem_errors A.coe c x y).mpr ⟨hxy.1, hcol⟩, rfl⟩)
  simpa using C.colorable

theorem errors_card_mem_edgeDistances (A : G.Subgraph) [Fintype A.verts]
    (c : A.verts → Bool) :
    (errors A.coe c).card ∈ Erdos74.SimpleGraph.edgeDistancesToBipartite A := by
  exact ⟨subgraphCutEdges A c, subgraphCutEdges_subset A c,
    subgraph_delete_cutEdges_bipartite A c, subgraphCutEdges_ncard A c⟩

/-- Any successful deletion contains the monochromatic edges of a binary cut. -/
theorem defect_le_deleted_edge_ncard (A : G.Subgraph) [Fintype A.verts]
    (E : Set (Sym2 V)) (hE : E ⊆ A.edgeSet)
    (hB : (A.deleteEdges E).coe.IsBipartite) : defect A.coe ≤ E.ncard := by
  classical
  let c : (A.deleteEdges E).coe.Coloring Bool := hB.toColoring (by simp)
  have hcut : subgraphCutEdges A c ⊆ E := by
    rintro _ ⟨e, he, rfl⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have he' := (mem_errors A.coe c x y).mp he
      by_contra hn
      exact c.valid ⟨he'.1, hn⟩ he'.2
  calc
    defect A.coe ≤ (errors A.coe c).card := defect_le_errors A.coe c
    _ = (subgraphCutEdges A c).ncard := (subgraphCutEdges_ncard A c).symm
    _ ≤ E.ncard := Set.ncard_le_ncard hcut
      ((subgraph_edgeSet_finite A (Set.toFinite _)).subset hE)

/-- On a finite subgraph the internal cut defect is exactly the Spec deletion distance. -/
theorem defect_eq_minEdgeDistToBipartite (A : G.Subgraph) [Fintype A.verts] :
    defect A.coe = Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  apply Nat.le_antisymm
  · have hne : (Erdos74.SimpleGraph.edgeDistancesToBipartite A).Nonempty :=
      ⟨_, errors_card_mem_edgeDistances A (fun _ => false)⟩
    obtain ⟨E, hE, hB, hcard⟩ := Nat.sInf_mem hne
    exact (defect_le_deleted_edge_ncard A E hE hB).trans_eq hcard
  · obtain ⟨c, hc⟩ := exists_optimal A.coe
    exact (Nat.sInf_le (errors_card_mem_edgeDistances A c)).trans_eq hc

/-- A uniform bound for all Spec distances on a fixed finite vertex set. -/
theorem minEdgeDistToBipartite_le_choose_two (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.verts.ncard.choose 2 := by
  classical
  letI : Fintype A.verts := hA.fintype
  rw [← defect_eq_minEdgeDistToBipartite A]
  calc
    defect A.coe ≤ (errors A.coe (fun _ => false)).card := defect_le_errors _ _
    _ ≤ A.coe.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono (badGraph_le _ _))
    _ ≤ (Fintype.card A.verts).choose 2 := A.coe.card_edgeFinset_le_card_choose_two
    _ = A.verts.ncard.choose 2 := by
      simp [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

/-- The exact-size set in Spec is bounded, including when it is empty. -/
theorem subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro k ⟨A, hcard, hA, rfl⟩
  simpa only [hcard] using minEdgeDistToBipartite_le_choose_two A hA

/-- A finite subgraph is below the Spec envelope at its exact number of vertices. -/
theorem minEdgeDistToBipartite_le_max (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤
      Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G A.verts.ncard := by
  exact le_csSup (subgraphEdgeDistsToBipartite_bddAbove G A.verts.ncard)
    ⟨A, rfl, hA, rfl⟩

/-- Restriction of a subgraph to a finite set of its vertices, viewed in the
original ambient graph.  The other vertices are absent, not counted as isolates. -/
def subgraphOnFinset (A : G.Subgraph) (s : Finset A.verts) : G.Subgraph :=
  A.induce (Subtype.val '' (s : Set A.verts))

theorem subgraphOnFinset_finite (A : G.Subgraph) (s : Finset A.verts) :
    (subgraphOnFinset A s).verts.Finite :=
  s.finite_toSet.image Subtype.val

@[simp] theorem subgraphOnFinset_ncard (A : G.Subgraph) (s : Finset A.verts) :
    (subgraphOnFinset A s).verts.ncard = s.card := by
  change (Subtype.val '' (s : Set A.verts)).ncard = s.card
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]

/-- The profile restriction and the ambient subgraph have the same defect:
adding back the isolated vertices does not change the cut minimum. -/
theorem defect_on_eq_minEdgeDist_subgraphOnFinset (A : G.Subgraph) [Fintype A.verts]
    (s : Finset A.verts) : defect (on A.coe s) =
      Erdos74.SimpleGraph.minEdgeDistToBipartite (subgraphOnFinset A s) := by
  classical
  let B := subgraphOnFinset A s
  letI : Fintype B.verts := (subgraphOnFinset_finite A s).fintype
  have hBA : B.verts ⊆ A.verts := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  let e : B.verts ↪ A.verts :=
    ⟨fun x => ⟨x.val, hBA x.property⟩,
      fun x y h => Subtype.ext (congrArg (fun z : A.verts => z.val) h)⟩
  have he : ∀ x : B.verts, e x ∈ s := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    have h : y = e x := Subtype.ext hxy
    exact h ▸ hy
  have hmap : B.coe.map e = on A.coe s := by
    ext x y
    constructor
    · rintro ⟨a, b, hab, rfl, rfl⟩
      exact ⟨hab.2.2, he a, he b⟩
    · rintro ⟨hxy, hx, hy⟩
      let a : B.verts := ⟨x.val, ⟨x, hx, rfl⟩⟩
      let b : B.verts := ⟨y.val, ⟨y, hy, rfl⟩⟩
      exact ⟨a, b, ⟨a.property, b.property, hxy⟩, Subtype.ext rfl, Subtype.ext rfl⟩
  rw [← hmap, defect_map, defect_eq_minEdgeDistToBipartite]

/-- A Spec envelope bounds the internal profile of every finite subgraph.
The envelope is first used at `s.card`; monotonicity is used only afterwards. -/
theorem profile_subgraph_le_of_spec_bound (f : ℕ → ℕ) (hfmono : Monotone f)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) [Fintype A.verts] (n : ℕ) : profile A.coe n ≤ f n := by
  apply (profile_le_iff A.coe n (f n)).mpr
  intro s hs
  rw [defect_on_eq_minEdgeDist_subgraphOnFinset]
  have h := minEdgeDistToBipartite_le_max (subgraphOnFinset A s)
    (subgraphOnFinset_finite A s)
  rw [subgraphOnFinset_ncard] at h
  exact h.trans ((hG s.card).trans (hfmono hs))

/-- Finite internal profile exclusion implies four-colorability for every
(possibly infinite) graph satisfying the Spec envelope, in the same universe.
No growth or plateau assumption on `f` is needed here. -/
theorem colorable_four_of_finite_profile_exclusion (f : ℕ → ℕ) (hfmono : Monotone f)
    (hfinite : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      (∀ n, profile H n ≤ f n) → H.Colorable 4) :
    ∀ (V : Type u) (G : SimpleGraph V),
      (∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) →
        G.Colorable 4 := by
  classical
  intro V G hG
  apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
  intro A hA
  letI : Fintype A.verts := hA.fintype
  exact (hfinite A.verts A.coe
    (fun n => profile_subgraph_le_of_spec_bound f hfmono hG A n)).some

/-- In particular, the Spec envelope cannot have infinite chromatic number. -/
theorem chromaticNumber_ne_top_of_finite_profile_exclusion
    (f : ℕ → ℕ) (hfmono : Monotone f)
    (hfinite : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      (∀ n, profile H n ≤ f n) → H.Colorable 4) :
    ∀ (V : Type u) (G : SimpleGraph V),
      (∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) →
        G.chromaticNumber ≠ ⊤ := by
  intro V G hG
  exact SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr
    ⟨4, colorable_four_of_finite_profile_exclusion f hfmono hfinite V G hG⟩

/-- The fixed-envelope negation to combine with a separately constructed `f`.
This statement uses only the definitions preceding the original conjecture. -/
theorem not_exists_infinite_chromatic_of_finite_profile_exclusion
    (f : ℕ → ℕ) (hfmono : Monotone f)
    (hfinite : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      (∀ n, profile H n ≤ f n) → H.Colorable 4) :
    ¬ ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n := by
  rintro ⟨V, G, htop, hG⟩
  exact chromaticNumber_ne_top_of_finite_profile_exclusion f hfmono hfinite V G hG htop

end E74

/-
# A divergent envelope excluding infinite chromatic number

The uniform plateau replacement gives the hypotheses of the abstract staircase
lemma for profiles of finite graphs that are not four-colorable.  The exact
finite-subgraph bridge and compactness then give the required counterexample.
-/

namespace E74

open SimpleGraph Filter
universe u

/-- Profiles of finite graphs which fail to admit four colors. -/
def badProfiles : Set (ℕ → ℕ) :=
  {p | ∃ (V : Type u) (inst : Fintype V) (G : SimpleGraph V),
    ¬ G.Colorable 4 ∧ @profile V inst G = p}

/-- A monotone divergent envelope that forces four colors on finite graphs. -/
theorem exists_finite_profile_envelope :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
        (∀ n, profile G n ≤ f n) → G.Colorable 4 := by
  have hmono : ∀ p ∈ badProfiles.{u}, Monotone p := by
    rintro p ⟨V, inst, G, _, rfl⟩
    letI : Fintype V := inst
    exact profile_monotone G
  have hbounded : ∀ p ∈ badProfiles.{u}, ∃ B, ∀ n, p n ≤ B := by
    rintro p ⟨V, inst, G, _, rfl⟩
    letI : Fintype V := inst
    exact ⟨defect G, profile_le_defect G⟩
  have hcap : ∀ B N p, p ∈ badProfiles.{u} → (∀ n, p n ≤ B) →
      p N = p (plateauBound B N) → 0 < p N →
      ∃ q ∈ badProfiles.{u}, ∀ n, q n ≤ min (p n) (p N) := by
    rintro B N p ⟨V, inst, G, hG, rfl⟩ hpB heq _
    letI : Fintype V := inst
    have hB : defect G ≤ B :=
      (profile_eq_defect G (n := Fintype.card V) le_rfl).symm.trans_le
        (hpB (Fintype.card V))
    obtain ⟨C, _, hprof, hextend⟩ := plateau_replacement G B N hB heq
    refine ⟨profile C, ?_, hprof⟩
    exact ⟨V ⊕ Bool, inferInstance, C, fun hc => hG (hextend hc), rfl⟩
  have hpositive : ∀ B p, p ∈ badProfiles.{u} →
      (∀ n, p n ≤ B) → 0 < p (2 * B) := by
    rintro B p ⟨V, inst, G, hG, rfl⟩ hpB
    letI : Fintype V := inst
    apply profile_pos_of_not_colorable_four G hG
    exact (profile_eq_defect G (n := Fintype.card V) le_rfl).symm.trans_le
      (hpB (Fintype.card V))
  obtain ⟨f, hfmono, hflim, havoid⟩ := exists_avoiding_staircase_of_moduli
    badProfiles.{u} (fun B => 2 * B) plateauBound
    hmono hbounded le_plateauBound hcap hpositive
  refine ⟨f, hfmono, hflim, ?_⟩
  intro V inst G hG
  by_contra hnot
  exact havoid (profile G) ⟨V, inst, G, hnot, rfl⟩ hG

/-- A genuinely divergent counterexample to the all-functions assertion. -/
theorem counterexample :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ¬ ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n := by
  obtain ⟨f, hfmono, hflim, hfinite⟩ := exists_finite_profile_envelope.{u}
  exact ⟨f, hflim,
    not_exists_infinite_chromatic_of_finite_profile_exclusion f hfmono hfinite⟩

end E74

theorem Erdos74.erdos_74.disproof : ¬ (type_of% @Erdos74.erdos_74) := by
  intro h
  obtain ⟨f, hf, hnone⟩ := E74.counterexample
  exact hnone (h f hf)
