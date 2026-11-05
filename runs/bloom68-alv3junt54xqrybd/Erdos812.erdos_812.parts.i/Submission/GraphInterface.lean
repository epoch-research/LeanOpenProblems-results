import Submission.RamseySupport

/-!
# Graph interface for the diagonal Ramsey property

The interface identifies the finite-set coloring definition with clique-free graphs and
clique-free complements. All statements here concern the definition, not the ratio conjecture.
-/

namespace Erdos812.Support

open Combinatorics

variable {V : Type*} [DecidableEq V]

/-- Homogeneity on the two-element subsets of a finite vertex set. -/
def PairHomogeneous (c : Finset V → Bool) (S : Finset V) (b : Bool) : Prop :=
  ∀ e : Finset V, e ⊆ S → e.card = 2 → c e = b

lemma pair_homogeneous_iff {c : Finset V → Bool} {S : Finset V} {b : Bool} :
    PairHomogeneous c S b ↔
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c {x, y} = b := by
  constructor
  · intro h x hx y hy hxy
    exact h {x, y} (by simp [Finset.insert_subset_iff, hx, hy]) (Finset.card_pair hxy)
  · intro h e he hcard
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    exact h x (he (by simp)) y (he (by simp)) hxy

/-- A coloring's true edges form a simple graph. -/
def graphOfColoring (c : Finset V → Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c {x, y} = true
  symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa [Finset.pair_comm] using h.2⟩
  loopless := by
    intro x h
    exact h.1 rfl

lemma graph_of_coloring_clique_iff {c : Finset V → Bool} {S : Finset V} :
    (graphOfColoring c).IsClique (S : Set V) ↔ PairHomogeneous c S true := by
  rw [SimpleGraph.isClique_iff, pair_homogeneous_iff]
  constructor
  · intro h x hx y hy hxy
    exact (h hx hy hxy).2
  · intro h x hx y hy hxy
    exact ⟨hxy, h x hx y hy hxy⟩

lemma graph_of_coloring_compl_clique_iff {c : Finset V → Bool} {S : Finset V} :
    (graphOfColoring c)ᶜ.IsClique (S : Set V) ↔ PairHomogeneous c S false := by
  rw [SimpleGraph.isClique_iff, pair_homogeneous_iff]
  constructor
  · intro h x hx y hy hxy
    have hnot := ((graphOfColoring c).compl_adj x y).mp (h hx hy hxy)
    apply Bool.eq_false_of_not_eq_true
    intro hc
    exact hnot.2 ⟨hxy, hc⟩
  · intro h x hx y hy hxy
    apply ((graphOfColoring c).compl_adj x y).mpr
    refine ⟨hxy, ?_⟩
    intro hc
    have hf := h x hx y hy hxy
    exact Bool.false_ne_true (hf.symm.trans hc.2)

/-- A graph colors a finite set true exactly when it contains an edge. -/
noncomputable def coloringOfGraph (G : SimpleGraph V) (e : Finset V) : Bool := by
  classical
  exact decide (∃ x ∈ e, ∃ y ∈ e, G.Adj x y)

lemma coloring_of_graph_pair (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    coloringOfGraph G {x, y} = decide (G.Adj x y) := by
  classical
  simp [coloringOfGraph, G.adj_comm]

lemma graph_of_coloring_of_graph (G : SimpleGraph V) :
    graphOfColoring (coloringOfGraph G) = G := by
  classical
  ext x y
  simp only [graphOfColoring, coloring_of_graph_pair, decide_eq_true_eq]
  exact and_iff_right_of_imp G.ne_of_adj

/-- The finite Ramsey property is precisely the clique-or-independent-set assertion. -/
lemma ramsey_property_iff_graph {n m : ℕ} :
    RamseyProperty 2 n m ↔
      ∀ G : SimpleGraph (Fin m),
        ∃ S : Finset (Fin m), G.IsNClique n S ∨ Gᶜ.IsNClique n S := by
  classical
  constructor
  · intro h G
    obtain ⟨S, hS, b, hb⟩ := h (coloringOfGraph G)
    refine ⟨S, ?_⟩
    cases b
    · right
      refine ⟨?_, hS⟩
      rw [← graph_of_coloring_of_graph G]
      exact graph_of_coloring_compl_clique_iff.mpr hb
    · left
      refine ⟨?_, hS⟩
      rw [← graph_of_coloring_of_graph G]
      exact graph_of_coloring_clique_iff.mpr hb
  · intro h c
    obtain ⟨S, hS⟩ := h (graphOfColoring c)
    rcases hS with hS | hS
    · exact ⟨S, hS.card_eq, true, graph_of_coloring_clique_iff.mp hS.isClique⟩
    · exact ⟨S, hS.card_eq, false, graph_of_coloring_compl_clique_iff.mp hS.isClique⟩

lemma not_ramsey_property_iff_graph {n m : ℕ} :
    ¬ RamseyProperty 2 n m ↔
      ∃ G : SimpleGraph (Fin m), G.CliqueFree n ∧ Gᶜ.CliqueFree n := by
  classical
  rw [ramsey_property_iff_graph]
  simp only [not_forall, not_exists, not_or, SimpleGraph.CliqueFree]
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨G, fun S => (hG S).1, fun S => (hG S).2⟩
  · rintro ⟨G, hr, hb⟩
    exact ⟨G, fun S => ⟨hr S, hb S⟩⟩

/-- There is a globally maximum graph avoiding both homogeneous targets. -/
lemma critical_graph {n : ℕ} (hn : 0 < n) :
    ∃ G : SimpleGraph (Fin (hypergraphRamsey 2 n - 1)),
      G.CliqueFree n ∧ Gᶜ.CliqueFree n := by
  apply not_ramsey_property_iff_graph.mp
  exact not_property_of_lt_ramsey (by have := graph_ramsey_pos hn; omega)

lemma graph_order_lt_ramsey {n m : ℕ} (G : SimpleGraph (Fin m))
    (hr : G.CliqueFree n) (hb : Gᶜ.CliqueFree n) :
    m < hypergraphRamsey 2 n :=
  order_lt_graph_ramsey_of_avoiding (not_ramsey_property_iff_graph.mpr ⟨G, hr, hb⟩)

end Erdos812.Support
