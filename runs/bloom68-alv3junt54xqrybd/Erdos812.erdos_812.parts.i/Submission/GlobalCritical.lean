import Submission.GraphInterface

/-!
# Global consequences for finite Ramsey-critical graphs

Relabeling by `Fin` gives the order bound for an arbitrary finite vertex type. Adding one
vertex with an arbitrary adjacency profile then gives global saturation immediately below
the Ramsey threshold. These are consequences of the defining Ramsey property only.
-/

namespace Erdos812.Support

open Combinatorics

variable {V : Type*}

/-- A finite graph avoiding an `n`-clique in both colors has order below the Ramsey number. -/
lemma graph_order_lt_ramsey_fintype [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (hr : G.CliqueFree n) (hb : Gᶜ.CliqueFree n) :
    Fintype.card V < hypergraphRamsey 2 n := by
  classical
  let e : Fin (Fintype.card V) ↪ V := (Fintype.equivFin V).symm.toEmbedding
  let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e
  let f : H ↪g G := SimpleGraph.Embedding.comap e G
  exact graph_order_lt_ramsey H (SimpleGraph.CliqueFree.comap f hr)
    (SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.complEquiv f) hb)

/-- The graph Ramsey property on any finite vertex type of sufficiently large order. -/
lemma graph_ramsey_of_card_ge [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (hcard : hypergraphRamsey 2 n ≤ Fintype.card V) :
    ∃ S : Finset V, G.IsNClique n S ∨ Gᶜ.IsNClique n S := by
  classical
  by_contra! h
  have hr : G.CliqueFree n := fun S => (h S).1
  have hb : Gᶜ.CliqueFree n := fun S => (h S).2
  exact (not_lt_of_ge hcard) (graph_order_lt_ramsey_fintype G hr hb)

/-- Adjoin a vertex `none` whose neighbors among the old vertices are exactly `A`. -/
def profileExtension (G : SimpleGraph V) (A : Finset V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | none, none => False
    | none, some v => v ∈ A
    | some v, none => v ∈ A
    | some v, some w => G.Adj v w
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.symm h
  loopless := by
    intro x
    cases x
    · exact id
    · exact G.loopless _

@[simp]
lemma profileExtension_adj_some (G : SimpleGraph V) (A : Finset V) (v w : V) :
    (profileExtension G A).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

@[simp]
lemma profileExtension_adj_none (G : SimpleGraph V) (A : Finset V) (v : V) :
    (profileExtension G A).Adj none (some v) ↔ v ∈ A := Iff.rfl

@[simp]
lemma profileExtension_comap_some (G : SimpleGraph V) (A : Finset V) :
    (profileExtension G A).comap Option.some = G := by
  ext v w
  rfl

@[simp]
lemma profileExtension_compl_comap_some (G : SimpleGraph V) (A : Finset V) :
    (profileExtension G A)ᶜ.comap Option.some = Gᶜ := by
  ext v w
  simp [SimpleGraph.compl_adj]

/-- A clique not using the added vertex pulls back to a clique of the same size. -/
private lemma option_clique_pullback {H : SimpleGraph (Option V)} {n : ℕ}
    {S : Finset (Option V)} (hS : H.IsNClique n S) (hNone : none ∉ S) :
    (H.comap Option.some).IsNClique n S.eraseNone := by
  refine ⟨?_, (Finset.card_eraseNone_of_not_mem hNone).trans hS.card_eq⟩
  intro v hv w hw hvw
  exact hS.isClique (Finset.mem_eraseNone.mp hv) (Finset.mem_eraseNone.mp hw)
    (by simpa only [ne_eq, Option.some.injEq] using hvw)

/-- Every one-vertex profile of a globally critical graph already contains a target
minus one in one of its two parts. -/
lemma global_saturation [Fintype V] [DecidableEq V] {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph V) (hr : G.CliqueFree n) (hb : Gᶜ.CliqueFree n)
    (hcard : Fintype.card V = hypergraphRamsey 2 n - 1) (A : Finset V) :
    (∃ S : Finset V, G.IsNClique (n - 1) S ∧ S ⊆ A) ∨
      (∃ S : Finset V, Gᶜ.IsNClique (n - 1) S ∧ S ⊆ Finset.univ \ A) := by
  classical
  let H := profileExtension G A
  have hpos : 0 < hypergraphRamsey 2 n := graph_ramsey_pos (by omega)
  have horder : hypergraphRamsey 2 n ≤ Fintype.card (Option V) := by
    rw [Fintype.card_option, hcard]
    omega
  obtain ⟨S, hS⟩ := graph_ramsey_of_card_ge H horder
  have hErase : (S.erase none).eraseNone = S.eraseNone := by
    ext v
    simp
  rcases hS with hS | hS
  · have hNone : none ∈ S := by
      by_contra hNone
      have hOld : G.IsNClique n S.eraseNone := by
        simpa [H] using option_clique_pullback hS hNone
      exact hr _ hOld
    left
    refine ⟨S.eraseNone, ?_, ?_⟩
    · have hOld := option_clique_pullback (hS.erase_of_mem hNone)
        (by simp)
      simpa [H, hErase] using hOld
    · intro v hv
      exact hS.isClique hNone (Finset.mem_eraseNone.mp hv) (by simp)
  · have hNone : none ∈ S := by
      by_contra hNone
      have hOld : Gᶜ.IsNClique n S.eraseNone := by
        simpa [H] using option_clique_pullback hS hNone
      exact hb _ hOld
    right
    refine ⟨S.eraseNone, ?_, ?_⟩
    · have hOld := option_clique_pullback (hS.erase_of_mem hNone)
        (by simp)
      simpa [H, hErase] using hOld
    · intro v hv
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hAdj := hS.isClique hNone (Finset.mem_eraseNone.mp hv) (by simp)
      exact ((H.compl_adj none (some v)).mp hAdj).2

/-- An `(n - 1)`-clique in an `n`-clique-free finite graph is a maximum clique. -/
lemma isMaximumClique_of_isNClique_pred [Fintype V] {n : ℕ} {G : SimpleGraph V}
    {S : Finset V} (hr : G.CliqueFree n) (hS : G.IsNClique (n - 1) S) :
    G.IsMaximumClique S := by
  classical
  refine ⟨hS.isClique, ?_⟩
  intro T hT
  by_contra hle
  have hlarge : n ≤ T.card := by
    have := hS.card_eq
    omega
  obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq hlarge
  exact hr U ⟨hT.subset (Finset.coe_subset.mpr hUT), hU⟩

/-- Every old vertex belongs to a target-minus-one clique. The profile is its closed
neighborhood, so the added vertex is an adjacent twin. A complement outcome would extend
with the original vertex to a forbidden clique; the same is true of a graph outcome that
does not contain the original vertex. -/
lemma critical_vertex_clique [Fintype V] {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph V)
    (hr : G.CliqueFree n) (hb : Gᶜ.CliqueFree n)
    (hcard : Fintype.card V = hypergraphRamsey 2 n - 1) (v : V) :
    ∃ S : Finset V, v ∈ S ∧ G.IsNClique (n - 1) S := by
  classical
  have hn1 : 1 ≤ n := by omega
  let A : Finset V := Finset.univ.filter (fun w => w = v ∨ G.Adj v w)
  have hA (w : V) : w ∈ A ↔ w = v ∨ G.Adj v w := by simp [A]
  rcases global_saturation hn G hr hb hcard A with ⟨S, hS, hSA⟩ | ⟨S, hS, hSA⟩
  · refine ⟨S, ?_, hS⟩
    by_contra hv
    have hAdj : ∀ w ∈ S, G.Adj v w := by
      intro w hw
      rcases (hA w).mp (hSA hw) with heq | hAdj
      · subst w
        exact False.elim (hv hw)
      · exact hAdj
    have hForbidden : G.IsNClique n (insert v S) := by
      simpa only [Nat.sub_add_cancel hn1] using hS.insert hAdj
    exact hr _ hForbidden
  · have hAdj : ∀ w ∈ S, Gᶜ.Adj v w := by
      intro w hw
      have hNotA : w ∉ A := (Finset.mem_sdiff.mp (hSA hw)).2
      apply (G.compl_adj v w).mpr
      refine ⟨?_, ?_⟩
      · intro heq
        exact hNotA ((hA w).mpr (Or.inl heq.symm))
      · intro hAdj
        exact hNotA ((hA w).mpr (Or.inr hAdj))
    have hForbidden : Gᶜ.IsNClique n (insert v S) := by
      simpa only [Nat.sub_add_cancel hn1] using hS.insert hAdj
    exact False.elim (hb _ hForbidden)

/-- Every vertex of a globally critical graph belongs to a maximum `(n - 1)`-clique
in each color. Applying the adjacent-twin argument to the complement gives the other color. -/
lemma critical_vertex_maximum_cliques [Fintype V] {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph V) (hr : G.CliqueFree n) (hb : Gᶜ.CliqueFree n)
    (hcard : Fintype.card V = hypergraphRamsey 2 n - 1) (v : V) :
    (∃ S : Finset V, v ∈ S ∧ G.IsNClique (n - 1) S ∧ G.IsMaximumClique S) ∧
      (∃ T : Finset V, v ∈ T ∧ Gᶜ.IsNClique (n - 1) T ∧ Gᶜ.IsMaximumClique T) := by
  obtain ⟨S, hvS, hS⟩ := critical_vertex_clique hn G hr hb hcard v
  obtain ⟨T, hvT, hT⟩ := critical_vertex_clique hn Gᶜ hb (by simpa using hr) hcard v
  exact ⟨⟨S, hvS, hS, isMaximumClique_of_isNClique_pred hr hS⟩,
    ⟨T, hvT, hT, isMaximumClique_of_isNClique_pred hb hT⟩⟩

/-- In particular, every old vertex lies in a maximal `(n - 1)`-clique of each color. -/
lemma critical_vertex_maximal_cliques [Fintype V] {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph V) (hr : G.CliqueFree n) (hb : Gᶜ.CliqueFree n)
    (hcard : Fintype.card V = hypergraphRamsey 2 n - 1) (v : V) :
    (∃ S : Finset V, v ∈ S ∧ G.IsNClique (n - 1) S ∧
      Maximal G.IsClique (S : Set V)) ∧
      (∃ T : Finset V, v ∈ T ∧ Gᶜ.IsNClique (n - 1) T ∧
        Maximal Gᶜ.IsClique (T : Set V)) := by
  obtain ⟨⟨S, hvS, hS, hMaxS⟩, ⟨T, hvT, hT, hMaxT⟩⟩ :=
    critical_vertex_maximum_cliques hn G hr hb hcard v
  exact ⟨⟨S, hvS, hS, SimpleGraph.IsMaximumClique.isMaximalClique S hMaxS⟩,
    ⟨T, hvT, hT, SimpleGraph.IsMaximumClique.isMaximalClique T hMaxT⟩⟩

end Erdos812.Support
