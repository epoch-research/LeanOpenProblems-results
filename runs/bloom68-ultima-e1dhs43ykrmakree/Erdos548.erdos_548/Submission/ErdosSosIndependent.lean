import Mathlib

/-!
# Independently verified reductions for Erdős–Sós

This file does not prove the full conjecture and does not import `Submission.Spec`.
It records the density-minimal induced-subgraph reduction and an elementary
consequence of the degree-sum formula. All inequalities use rational numbers.
-/

open Finset SimpleGraph Classical

namespace ErdosSosIndependent

variable {V : Type*} [Fintype V]

/-- The edges of `G` whose two endpoints belong to `s`. -/
noncomputable def edgesOn (G : SimpleGraph V) (s : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset ∩ s.sym2

lemma edgesOn_mono (G : SimpleGraph V) {s t : Finset V} (h : s ⊆ t) :
    edgesOn G s ⊆ edgesOn G t := by
  classical
  exact Finset.inter_subset_inter (Finset.Subset.refl _) (Finset.sym2_mono h)

@[simp] lemma edgesOn_empty (G : SimpleGraph V) : edgesOn G ∅ = ∅ := by
  classical
  simp [edgesOn]

@[simp] lemma edgesOn_univ (G : SimpleGraph V) : edgesOn G univ = G.edgeFinset := by
  classical
  simp [edgesOn, Finset.sym2_univ]

/-- `edgesOn` counts the conventional induced graph, not a modified graph notion. -/
lemma card_edgesOn (G : SimpleGraph V) (s : Finset V) :
    (edgesOn G s).card = (G.induce (s : Set V)).edgeFinset.card := by
  classical
  have h := G.map_edgeFinset_induce (s := (s : Set V))
  have hc := congrArg Finset.card h
  simpa [edgesOn, SimpleGraph.edgeFinset, Set.toFinset_card,
    ← Nat.card_eq_fintype_card] using hc.symm

/-- A finite positive-density witness contains one of minimum cardinality. -/
lemma exists_density_minimal_set (G : SimpleGraph V) (a : ℚ)
    (h : a * Fintype.card V < (G.edgeFinset.card : ℚ)) :
    ∃ s : Finset V, s.Nonempty ∧
      a * s.card < (edgesOn G s).card ∧
      ∀ t : Finset V, t.card < s.card →
        (edgesOn G t).card ≤ a * t.card := by
  classical
  let candidates : Finset (Finset V) :=
    univ.filter (fun s => a * s.card < (edgesOn G s).card)
  have hc : (univ : Finset V) ∈ candidates := by
    simpa [candidates] using h
  obtain ⟨s, hs, hmin⟩ :=
    candidates.exists_min_image Finset.card ⟨univ, hc⟩
  have hsden : a * s.card < (edgesOn G s).card := (mem_filter.mp hs).2
  have hsne : s.Nonempty := by
    by_contra hn
    have he : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [he] at hsden
  refine ⟨s, hsne, hsden, ?_⟩
  intro t ht
  by_contra hle
  have htden : a * t.card < (edgesOn G t).card := lt_of_not_ge hle
  have htc : t ∈ candidates := mem_filter.mpr ⟨mem_univ _, htden⟩
  exact (not_le_of_gt ht) (hmin t htc)

/--
In a minimum-cardinality density witness, every nonempty vertex set `t` loses
more than `a * |t|` edges when deleted. The set difference counts precisely
those edges with at least one endpoint in `t` and both endpoints in `s`.
-/
lemma exists_incidence_dense_set (G : SimpleGraph V) (a : ℚ)
    (h : a * Fintype.card V < (G.edgeFinset.card : ℚ)) :
    ∃ s : Finset V, s.Nonempty ∧
      a * s.card < (edgesOn G s).card ∧
      ∀ t : Finset V, t ⊆ s → t.Nonempty →
        a * t.card < ((edgesOn G s \ edgesOn G (s \ t)).card : ℚ) := by
  classical
  obtain ⟨s, hsne, hsden, hmin⟩ := exists_density_minimal_set G a h
  refine ⟨s, hsne, hsden, ?_⟩
  intro t hts htne
  have hv : (s \ t).card + t.card = s.card := card_sdiff_add_card_eq_card hts
  have htpos : 0 < t.card := card_pos.mpr htne
  have hlt : (s \ t).card < s.card := by omega
  have hrem := hmin (s \ t) hlt
  have he :
      (edgesOn G s \ edgesOn G (s \ t)).card + (edgesOn G (s \ t)).card =
        (edgesOn G s).card :=
    card_sdiff_add_card_eq_card (edgesOn_mono G sdiff_subset)
  have hvq : ((s \ t).card : ℚ) + t.card = s.card := by exact_mod_cast hv
  have heq :
      ((edgesOn G s \ edgesOn G (s \ t)).card : ℚ) +
        (edgesOn G (s \ t)).card = (edgesOn G s).card := by
    exact_mod_cast he
  have hva := congrArg (fun x : ℚ => a * x) hvq
  simp only [mul_add] at hva
  linarith

/-- Average degree strictly greater than `k - 1` gives a vertex of degree at
least `k`; it does not give minimum degree at least `k`. -/
lemma exists_degree_ge_of_density (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ((k : ℚ) - 1) / 2 * Fintype.card V < (G.edgeFinset.card : ℚ)) :
    ∃ v : V, k ≤ G.degree v := by
  classical
  by_contra! hn
  have hd (v : V) : (G.degree v : ℚ) ≤ (k : ℚ) - 1 := by
    have hv : (G.degree v : ℚ) + 1 ≤ k := by
      exact_mod_cast Nat.succ_le_of_lt (hn v)
    linarith
  have hs : (∑ v : V, (G.degree v : ℚ)) ≤
      ∑ _v : V, ((k : ℚ) - 1) := Finset.sum_le_sum (fun v _ => hd v)
  have he : (∑ v : V, (G.degree v : ℚ)) = 2 * (G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  simp only [sum_const, card_univ, nsmul_eq_mul] at hs
  nlinarith

/-- Weighted deletion: the cost of deleting vertex `v` may depend on `v`. -/
lemma exists_weighted_incidence_dense_set (G : SimpleGraph V) (w : V → ℚ)
    (h : (∑ v : V, w v) < (G.edgeFinset.card : ℚ)) :
    ∃ s : Finset V, s.Nonempty ∧
      (∑ v ∈ s, w v) < (edgesOn G s).card ∧
      ∀ t : Finset V, t ⊆ s → t.Nonempty →
        (∑ v ∈ t, w v) < ((edgesOn G s \ edgesOn G (s \ t)).card : ℚ) := by
  classical
  let candidates : Finset (Finset V) :=
    univ.filter (fun s => (∑ v ∈ s, w v) < (edgesOn G s).card)
  have hc : (univ : Finset V) ∈ candidates := by
    simpa [candidates] using h
  obtain ⟨s, hs, hmin⟩ :=
    candidates.exists_min_image Finset.card ⟨univ, hc⟩
  have hsden : (∑ v ∈ s, w v) < (edgesOn G s).card := (mem_filter.mp hs).2
  have hsne : s.Nonempty := by
    by_contra hn
    have he : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [he] at hsden
  refine ⟨s, hsne, hsden, ?_⟩
  intro t hts htne
  have hv : (s \ t).card + t.card = s.card := card_sdiff_add_card_eq_card hts
  have htpos : 0 < t.card := card_pos.mpr htne
  have hlt : (s \ t).card < s.card := by omega
  have hrem : ((edgesOn G (s \ t)).card : ℚ) ≤ ∑ v ∈ s \ t, w v := by
    by_contra hn
    have hp : s \ t ∈ candidates := mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hn⟩
    exact (not_le_of_gt hlt) (hmin _ hp)
  have he :
      (edgesOn G s \ edgesOn G (s \ t)).card + (edgesOn G (s \ t)).card =
        (edgesOn G s).card :=
    card_sdiff_add_card_eq_card (edgesOn_mono G sdiff_subset)
  have heq :
      ((edgesOn G s \ edgesOn G (s \ t)).card : ℚ) +
        (edgesOn G (s \ t)).card = (edgesOn G s).card := by
    exact_mod_cast he
  have hw : (∑ v ∈ s \ t, w v) + ∑ v ∈ t, w v = ∑ v ∈ s, w v :=
    Finset.sum_sdiff hts
  linarith

/-- The edges lost on deleting a vertex are in bijection with its neighbors
in the chosen vertex set. -/
lemma card_edgesOn_delete_vertex (G : SimpleGraph V) (s : Finset V) (v : V) (hv : v ∈ s) :
    (edgesOn G s \ edgesOn G (s \ {v})).card = (G.neighborFinset v ∩ s).card := by
  classical
  have hinj : Function.Injective (fun u : V => s(v, u)) := by
    intro x y hxy
    rcases Sym2.eq_iff.mp hxy with hxy | hxy
    · exact hxy.2
    · exact hxy.2.trans hxy.1
  have he : edgesOn G s \ edgesOn G (s \ {v}) =
      (G.neighborFinset v ∩ s).image (fun u => s(v, u)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [edgesOn, mem_sdiff, mem_inter, mem_edgeFinset,
        mem_edgeSet, mk_mem_sym2_iff, mem_singleton, mem_image,
        mem_neighborFinset, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨hxy, hx, hy⟩, hn⟩
        have heq : x = v ∨ y = v := by tauto
        rcases heq with rfl | rfl
        · exact ⟨y, ⟨hxy, hy⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨x, ⟨hxy.symm, hx⟩, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨u, ⟨hvu, hu⟩, heq⟩
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [adj_comm]
  rw [he, Finset.card_image_of_injective _ hinj]

/-- The finite-set degree in the preceding lemma is the usual induced degree. -/
lemma card_neighbors_inter (G : SimpleGraph V) (s : Finset V) (v : (s : Set V)) :
    (G.neighborFinset v ∩ s).card = (G.induce (s : Set V)).degree v := by
  classical
  have h := G.map_neighborFinset_induce v
  simpa only [Finset.card_map, Finset.toFinset_coe,
    SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using (congrArg Finset.card h).symm

/-- A conventional induced subgraph satisfying all specified weighted degree
lower bounds. This is the weighted pruning lemma used in the bipartite case. -/
lemma exists_induced_degree_gt_weight (G : SimpleGraph V) (w : V → ℚ)
    (h : (∑ v : V, w v) < (G.edgeFinset.card : ℚ)) :
    ∃ s : Finset V, s.Nonempty ∧
      (∑ v ∈ s, w v) < (edgesOn G s).card ∧
      ∀ v : (s : Set V), w v < ((G.induce (s : Set V)).degree v : ℚ) := by
  classical
  obtain ⟨s, hs, hd, hw⟩ := exists_weighted_incidence_dense_set G w h
  refine ⟨s, hs, hd, ?_⟩
  intro v
  have hv := hw {v.val} (singleton_subset_iff.mpr v.property) (singleton_nonempty _)
  simpa [card_edgesOn_delete_vertex G s v.val v.property,
    card_neighbors_inter G s v] using hv

/-- Density pruning only gives minimum degree greater than half the original
average-degree threshold. -/
lemma exists_density_core (G : SimpleGraph V) (a : ℚ)
    (h : a * Fintype.card V < (G.edgeFinset.card : ℚ)) :
    ∃ s : Finset V, s.Nonempty ∧
      a * s.card < (edgesOn G s).card ∧
      ∀ v : (s : Set V), a < ((G.induce (s : Set V)).degree v : ℚ) := by
  have hw : (∑ _v : V, a) < (G.edgeFinset.card : ℚ) := by
    simpa [mul_comm] using h
  obtain ⟨s, hs, hd, hv⟩ := exists_induced_degree_gt_weight G (fun _ => a) hw
  exact ⟨s, hs, by simpa [mul_comm] using hd, hv⟩

/-- The exact safe Erdős–Sós core: minimum degree at least `ceil (k / 2)`,
maximum degree at least `k`, and the strict density inequality is retained. -/
lemma exists_erdos_sos_core (G : SimpleGraph V) (k : ℕ)
    (h : ((k : ℚ) - 1) / 2 * Fintype.card V < (G.edgeFinset.card : ℚ)) :
    ∃ s : Finset V, s.Nonempty ∧
      ((k : ℚ) - 1) / 2 * s.card < (edgesOn G s).card ∧
      (∀ v : (s : Set V), k ≤ 2 * (G.induce (s : Set V)).degree v) ∧
      ∃ v : (s : Set V), k ≤ (G.induce (s : Set V)).degree v := by
  classical
  obtain ⟨s, hs, hd, hv⟩ := exists_density_core G (((k : ℚ) - 1) / 2) h
  refine ⟨s, hs, hd, ?_, ?_⟩
  · intro v
    have hvq := hv v
    have hiq : (k : ℚ) < 2 * ((G.induce (s : Set V)).degree v : ℚ) + 1 := by
      linarith
    have hin : k < 2 * (G.induce (s : Set V)).degree v + 1 := by
      exact_mod_cast hiq
    omega
  · apply exists_degree_ge_of_density (G.induce (s : Set V)) k
    have hc : Fintype.card (s : Set V) = s.card := by
      rw [← Nat.card_eq_fintype_card]
      simp
    simpa only [hc, ← card_edgesOn] using hd

end ErdosSosIndependent
