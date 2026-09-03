import Submission.CommonMarkedForest
import Submission.ErdosSosIndependent

set_option autoImplicit false

/-!
# Exact-apex embeddings and the high-degree case of Erdős–Sós

Deleting a vertex `u` of a tree leaves a forest with one neighbor of `u` in
each component.  The common-list forest theorem embeds these component roots
in the neighborhood of a specified host vertex `s`; adjoining `u ↦ s` then
embeds the tree.  Combining this with the strict-density core proves the
Erdős–Sós conclusion for trees with a vertex of degree at least `k / 2 + 1`.

Copies are injective graph homomorphisms, not induced embeddings.  This file
does not import `Submission.Spec` and does not claim the full conjecture.
-/

open Finset SimpleGraph Classical

namespace ErdosSosHighDegree

universe u v

section DeletedTree

variable {V : Type u} {T : SimpleGraph V}

/-- Every vertex left after deletion can reach a neighbor of the deleted vertex
without passing through that vertex. -/
lemma exists_neighbor_reachable_delete (hT : T.Connected) (u : V)
    (x : ({u}ᶜ : Set V)) :
    ∃ r : ({u}ᶜ : Set V), T.Adj u r ∧ (T.induce {u}ᶜ).Reachable r x := by
  obtain ⟨p, hp⟩ := hT.exists_isPath u x.val
  obtain ⟨y, huy, p, rfl⟩ := Walk.exists_eq_cons_of_ne (Ne.symm x.property) p
  have hu : u ∉ p.support := ((Walk.cons_isPath_iff _ _).mp hp).2
  have hs : ∀ z ∈ p.support, z ∈ ({u}ᶜ : Set V) := by
    intro z hz hzu
    exact hu (hzu ▸ hz)
  refine ⟨⟨y, huy.ne.symm⟩, huy, ?_⟩
  exact ⟨(p.induce {u}ᶜ hs).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- Two neighbors of a vertex in an acyclic graph cannot lie in the same
component after that vertex is deleted. -/
lemma neighbor_eq_of_reachable_delete (hT : T.IsAcyclic) (u : V)
    {x y : ({u}ᶜ : Set V)} (hx : T.Adj u x) (hy : T.Adj u y)
    (hxy : (T.induce {u}ᶜ).Reachable x y) : x = y := by
  obtain ⟨p, hp⟩ := hxy.exists_isPath
  let q : T.Walk x.val y.val := p.map (Embedding.induce {u}ᶜ).toHom
  have hq : q.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hp
  have hu : u ∉ q.support := by
    simp only [q, Walk.support_map, List.mem_map]
    rintro ⟨z, _, hz⟩
    exact z.property hz
  have hcons : (q.cons hx).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hq, hu⟩
  have he : q.cons hx = Walk.cons hy Walk.nil :=
    congrArg Subtype.val (hT.path_unique ⟨_, hcons⟩ (Path.singleton hy))
  apply Subtype.ext
  simpa using congrArg (fun p : T.Walk u y.val => p.getVert 1) he

/-- Each component of a vertex-deleted tree contains exactly one neighbor of
the deleted vertex.  Existence uses connectedness; uniqueness uses acyclicity. -/
theorem existsUnique_neighbor_in_component (hT : T.IsTree) (u : V)
    (C : (T.induce {u}ᶜ).ConnectedComponent) :
    ∃! r : ({u}ᶜ : Set V), r ∈ C.supp ∧ T.Adj u r := by
  obtain ⟨x, hx⟩ := C.nonempty_supp
  obtain ⟨r, hr, hrx⟩ := exists_neighbor_reachable_delete hT.isConnected u x
  have hrC : r ∈ C.supp := (ConnectedComponent.sound hrx).trans hx
  refine ⟨r, ⟨hrC, hr⟩, ?_⟩
  intro y hy
  exact neighbor_eq_of_reachable_delete hT.IsAcyclic u hy.2 hr
    (C.reachable_of_mem_supp hy.1 hrC)

end DeletedTree

section DeletionCounts

variable {V : Type u} [Fintype V] (T : SimpleGraph V)

/-- Deleting a vertex removes exactly its degree many edges. -/
lemma edges_delete_vertex (u : V) :
    (T.induce {u}ᶜ).edgeFinset.card = T.edgeFinset.card - T.degree u := by
  rw [T.card_edgeFinset_induce_compl_singleton, T.card_edgeFinset_deleteIncidenceSet]

/-- Deleting a vertex of a finite tree leaves as many vertices as the tree had edges. -/
lemma card_delete_vertex (hT : T.IsTree) (u : V) :
    Fintype.card ({u}ᶜ : Set V) = T.edgeFinset.card := by
  rw [Fintype.card_compl_set,
    show Fintype.card ({u} : Set V) = 1 from Fintype.card_unique]
  have ht := hT.card_edgeFinset
  omega

/-- The exact change in the degree of a surviving vertex. -/
lemma degree_delete_vertex (u : V) (x : ({u}ᶜ : Set V)) :
    (T.induce {u}ᶜ).degree x = T.degree x.val - (if T.Adj x.val u then 1 else 0) := by
  have he : (T.induce {u}ᶜ).degree x = (T.neighborFinset x.val \ {u}).card := by
    have h := congrArg Finset.card (T.map_neighborFinset_induce (s := {u}ᶜ) x)
    simpa [Finset.sdiff_eq_inter_compl] using h
  rw [he, Finset.sdiff_singleton_eq_erase]
  by_cases hx : T.Adj x.val u
  · rw [if_pos hx, Finset.card_erase_of_mem (T.mem_neighborFinset _ _ |>.mpr hx),
      T.card_neighborFinset_eq_degree]
  · rw [if_neg hx, Finset.erase_eq_of_notMem (by simpa using hx),
      T.card_neighborFinset_eq_degree, Nat.sub_zero]

/-- A surviving vertex loses at most one neighbor. -/
lemma degree_le_delete_vertex_add_one (u : V) (x : ({u}ᶜ : Set V)) :
    T.degree x.val ≤ (T.induce {u}ᶜ).degree x + 1 := by
  rw [degree_delete_vertex]
  split_ifs <;> omega

end DeletionCounts

section ApexList

variable {W : Type v} [Fintype W] (G : SimpleGraph W) (s : W)

/-- The neighborhood of the apex, viewed inside the apex-deleted host. -/
noncomputable def apexList : Finset ({s}ᶜ : Set W) :=
  univ.filter (fun x => G.Adj s x.val)

@[simp] lemma mem_apexList (x : ({s}ᶜ : Set W)) :
    x ∈ apexList G s ↔ G.Adj s x.val := by
  simp [apexList]

lemma card_apexList : (apexList G s).card = G.degree s := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact (G.mem_neighborFinset _ _).mpr ((mem_apexList G s x).mp hx)
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    have hsx := (G.mem_neighborFinset _ _).mp hx
    exact ⟨⟨x, hsx.ne.symm⟩, (mem_apexList G s _).mpr hsx, rfl⟩

end ApexList

section ApexExtension

variable {V : Type u} {W : Type v} (T : SimpleGraph V) (G : SimpleGraph W)

/-- Adjoin the deleted vertices to a copy, provided all neighbors of the source
apex already map to neighbors of the target apex. -/
lemma extend_apex (u : V) (s : W)
    (g : (T.induce {u}ᶜ).Copy (G.induce {s}ᶜ))
    (hadj : ∀ x : ({u}ᶜ : Set V), T.Adj u x.val → G.Adj s (g x).val) :
    ∃ f : T.Copy G, f u = s := by
  let f : V → W := fun x => if hx : x = u then s else (g ⟨x, hx⟩).val
  refine ⟨⟨⟨f, ?_⟩, ?_⟩, ?_⟩
  · intro x y hxy
    by_cases hx : x = u
    · subst x
      have hy : y ≠ u := hxy.ne.symm
      simpa [f, hy] using hadj ⟨y, hy⟩ hxy
    · by_cases hy : y = u
      · subst y
        simpa [f, hx] using (hadj ⟨x, hx⟩ hxy.symm).symm
      · simpa [f, hx, hy] using g.toHom.map_rel'
          (show (T.induce {u}ᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
  · intro x y hxy
    by_cases hx : x = u
    · by_cases hy : y = u
      · exact hx.trans hy.symm
      · have he : s = (g ⟨y, hy⟩).val := by simpa [f, hx, hy] using hxy
        exact ((g ⟨y, hy⟩).property he.symm).elim
    · by_cases hy : y = u
      · have he : (g ⟨x, hx⟩).val = s := by simpa [f, hx, hy] using hxy
        exact ((g ⟨x, hx⟩).property he).elim
      · have he : (g ⟨x, hx⟩).val = (g ⟨y, hy⟩).val := by
          simpa [f, hx, hy] using hxy
        exact congrArg Subtype.val (g.injective (Subtype.ext he))
  · simp [f]

end ApexExtension

section ExactApex

variable {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (T : SimpleGraph V) (G : SimpleGraph W)

/-- **Exact-apex theorem.** A `k`-edge tree with a specified vertex `u` embeds
with `u ↦ s` if `s` has at least `k` neighbors and every vertex of `G - s`
has degree at least `k - T.degree u` in `G - s`. -/
theorem exact_apex (hT : T.IsTree) (u : V) (s : W) {k : ℕ}
    (hk : T.edgeFinset.card = k) (hs : k ≤ G.degree s)
    (hdeg : ∀ x : ({s}ᶜ : Set W), k - T.degree u ≤ (G.induce {s}ᶜ).degree x) :
    ∃ f : T.Copy G, f u = s := by
  let F := T.induce {u}ᶜ
  choose roots hroots using (fun C : F.ConnectedComponent =>
    (existsUnique_neighbor_in_component hT u C).exists)
  obtain ⟨g, hg⟩ := CommonMarkedForest.common_list_forest_roots F
    (hT.IsAcyclic.induce _) roots (fun C => (hroots C).1)
    (G.induce {s}ᶜ) (apexList G s)
    (by simpa [F, edges_delete_vertex, hk] using hdeg)
    (by simpa only [card_delete_vertex T hT u, hk, card_apexList] using hs)
  apply extend_apex T G u s g
  intro x hx
  let C := F.connectedComponentMk x
  have he : x = roots C := (existsUnique_neighbor_in_component hT u C).unique
    ⟨ConnectedComponent.connectedComponentMk_mem, hx⟩ (hroots C)
  have hm := hg C
  rw [← he] at hm
  exact (mem_apexList G s _).mp hm

/-- A convenient sufficient condition before deleting the host apex: every
host degree is at least `k - T.degree u + 1`. -/
theorem exact_apex_of_degree (hT : T.IsTree) (u : V) (s : W) {k : ℕ}
    (hk : T.edgeFinset.card = k) (hs : k ≤ G.degree s)
    (hdeg : ∀ x : W, k - T.degree u + 1 ≤ G.degree x) :
    ∃ f : T.Copy G, f u = s := by
  apply exact_apex T G hT u s hk hs
  intro x
  have h₁ := hdeg x.val
  have h₂ := degree_le_delete_vertex_add_one G s x
  omega

/-- The minimum-degree version of the exact-apex theorem. -/
theorem exact_apex_of_minDegree (hT : T.IsTree) (u : V) (s : W) {k : ℕ}
    (hk : T.edgeFinset.card = k) (hs : k ≤ G.degree s)
    (hdeg : k - T.degree u + 1 ≤ G.minDegree) :
    ∃ f : T.Copy G, f u = s :=
  exact_apex_of_degree T G hT u s hk hs
    (fun x => hdeg.trans (G.minDegree_le_degree x))

end ExactApex

section Density

variable {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (T : SimpleGraph V) (G : SimpleGraph W)

/-- The finite edge count agrees with the conventional edge-set cardinality. -/
lemma card_edgeFinset_eq_ncard : G.edgeFinset.card = G.edgeSet.ncard := by
  rw [Set.ncard_eq_toFinset_card, Set.toFinite_toFinset]
  rfl

/-- **High-degree Erdős–Sós, specified vertex.** Strict density suffices for a
`k`-edge tree with a specified vertex of degree at least `floor (k / 2) + 1`.
The host and tree may have arbitrary finite vertex types. -/
theorem isContained_of_density_of_degree (hT : T.IsTree) {k : ℕ}
    (hk : T.edgeFinset.card = k)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card W < (G.edgeSet.ncard : ℚ))
    (u : V) (hu : k / 2 + 1 ≤ T.degree u) : T.IsContained G := by
  obtain ⟨S, _hS, _hden, hmin, s, hs⟩ :=
    ErdosSosIndependent.exists_erdos_sos_core G k
      (by simpa only [card_edgeFinset_eq_ncard] using hdensity)
  have hd : T.degree u ≤ k := hk ▸ T.degree_le_card_edgeFinset u
  obtain ⟨f, _hf⟩ := exact_apex_of_degree T (G.induce (S : Set W)) hT u s hk hs
    (by
      intro x
      have hx := hmin x
      omega)
  exact ⟨(Copy.induce G (S : Set W)).comp f⟩

/-- Strict-density containment when the tree has a sufficiently high-degree vertex. -/
theorem isContained_of_density_of_exists_degree (hT : T.IsTree) {k : ℕ}
    (hk : T.edgeFinset.card = k)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card W < (G.edgeSet.ncard : ℚ))
    (hdegree : ∃ u : V, k / 2 + 1 ≤ T.degree u) : T.IsContained G := by
  obtain ⟨u, hu⟩ := hdegree
  exact isContained_of_density_of_degree T G hT hk hdensity u hu

/-- The maximum-degree formulation of the high-degree Erdős–Sós result. -/
theorem isContained_of_density_of_maxDegree (hT : T.IsTree) {k : ℕ}
    (hk : T.edgeFinset.card = k)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card W < (G.edgeSet.ncard : ℚ))
    (hdegree : k / 2 + 1 ≤ T.maxDegree) : T.IsContained G := by
  letI : Nonempty V := hT.isConnected.nonempty
  obtain ⟨u, hu⟩ := T.exists_maximal_degree_vertex
  exact isContained_of_density_of_degree T G hT hk hdensity u (hu ▸ hdegree)

end Density

section FiniteInterfaces

/-- Strict-density Erdős–Sós for trees on `Fin (k + 1)` with a vertex of degree
at least `floor (k / 2) + 1`.  No additional host-order hypothesis is needed. -/
theorem erdos_sos_highDegree_strict (n k : ℕ) (G : SimpleGraph (Fin n))
    (hdensity : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree)
    (hdegree : ∃ u, k / 2 + 1 ≤ T.degree u) : T.IsContained G := by
  have hk : T.edgeFinset.card = k := by
    have ht := hT.card_edgeFinset
    simp only [Fintype.card_fin] at ht
    omega
  exact isContained_of_density_of_exists_degree T G hT hk
    (by simpa only [Fintype.card_fin] using hdensity) hdegree

/-- The original `((k - 1) / 2) * n + 1` density hypothesis, with the
high-degree restriction on the tree.  This is only that restricted case,
not the full Erdős–Sós conjecture. -/
theorem erdos_sos_highDegree :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree →
          (∃ u, k / 2 + 1 ≤ T.degree u) → T.IsContained G := by
  intro n k _hn G hdensity T hT hdegree
  apply erdos_sos_highDegree_strict n k G (by linarith) T hT hdegree

/-- Strict-density `Fin` interface using maximum degree. -/
theorem erdos_sos_maxDegree_strict (n k : ℕ) (G : SimpleGraph (Fin n))
    (hdensity : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree)
    (hdegree : k / 2 + 1 ≤ T.maxDegree) : T.IsContained G := by
  obtain ⟨u, hu⟩ := T.exists_maximal_degree_vertex
  exact erdos_sos_highDegree_strict n k G hdensity T hT ⟨u, hu ▸ hdegree⟩

/-- The original density hypothesis, with the maximum-degree restriction. -/
theorem erdos_sos_maxDegree :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree →
          k / 2 + 1 ≤ T.maxDegree → T.IsContained G := by
  intro n k _hn G hdensity T hT hdegree
  exact erdos_sos_maxDegree_strict n k G (by linarith) T hT hdegree

end FiniteInterfaces

end ErdosSosHighDegree

-- Transitive kernel-dependency audit for the structural and final interfaces.
#print axioms ErdosSosHighDegree.existsUnique_neighbor_in_component
#print axioms ErdosSosHighDegree.edges_delete_vertex
#print axioms ErdosSosHighDegree.card_delete_vertex
#print axioms ErdosSosHighDegree.degree_delete_vertex
#print axioms ErdosSosHighDegree.exact_apex
#print axioms ErdosSosHighDegree.exact_apex_of_degree
#print axioms ErdosSosHighDegree.exact_apex_of_minDegree
#print axioms ErdosSosHighDegree.isContained_of_density_of_degree
#print axioms ErdosSosHighDegree.isContained_of_density_of_exists_degree
#print axioms ErdosSosHighDegree.isContained_of_density_of_maxDegree
#print axioms ErdosSosHighDegree.erdos_sos_highDegree_strict
#print axioms ErdosSosHighDegree.erdos_sos_highDegree
#print axioms ErdosSosHighDegree.erdos_sos_maxDegree_strict
#print axioms ErdosSosHighDegree.erdos_sos_maxDegree
