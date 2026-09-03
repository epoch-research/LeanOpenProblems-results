import Mathlib

/-!
A statement-only formulation of Erdős Problem 74, with finite edge sets made explicit.
No proof or disproof of the problem is asserted here.

Also proved: if the endpoints of the monochromatic edges of a two-colouring induce
 a bipartite graph, the original graph is three-colourable.
-/

open Filter SimpleGraph

namespace Erdos74Analysis

universe u

/-- Every finite subgraph can be made bipartite by deleting at most `f` of its edges.
`Sym2 V` counts unordered edges, not ordered pairs, and `Finset` makes finiteness explicit. -/
def HereditaryEdgeBound {V : Type u} (G : SimpleGraph V) (f : ℕ → ℕ) : Prop :=
  ∀ A : G.Subgraph, A.verts.Finite →
    ∃ D : Finset (Sym2 V),
      (D : Set (Sym2 V)) ⊆ A.edgeSet ∧
      D.card ≤ f A.verts.ncard ∧
      (A.deleteEdges (D : Set (Sym2 V))).coe.Colorable 2

/-- The question, as a proposition rather than an unproved theorem. -/
def Statement : Prop :=
  ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    ∃ (V : Type u) (G : SimpleGraph V),
      (∀ k : ℕ, ¬ G.Colorable k) ∧ HereditaryEdgeBound G f

theorem noFiniteColoring_iff_top {V : Type u} (G : SimpleGraph V) :
    (∀ k : ℕ, ¬ G.Colorable k) ↔ G.chromaticNumber = ⊤ := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, hk⟩ := SimpleGraph.chromaticNumber_ne_top_iff_exists.mp hn
    exact h k hk
  · intro h k hk
    exact (SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨k, hk⟩) h

/-- The endpoints of the edges left monochromatic by an arbitrary two-colouring. -/
def badSupport {V : Type u} (G : SimpleGraph V) (p : V → Fin 2) : Set V :=
  {v | ∃ w, G.Adj v w ∧ p v = p w}

/-- An independent set meeting every monochromatic edge gives a third colour. -/
theorem colorable_three_of_independent_cover {V : Type u} (G : SimpleGraph V)
    (p : V → Fin 2) (S : Set V)
    (hind : ∀ {v w : V}, G.Adj v w → v ∈ S → w ∈ S → False)
    (hcover : ∀ {v w : V}, G.Adj v w → p v = p w → v ∈ S ∨ w ∈ S) :
    G.Colorable 3 := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (fun v ↦ if v ∈ S then (2 : Fin 3) else (p v).castSucc) ?_⟩
  intro v w hadj
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
  · exact (hind hadj hv hw).elim
  · simp only [if_pos hv, if_neg hw]
    intro heq
    have heq' := congrArg Fin.val heq
    have hlt := (p w).isLt
    change 2 = (p w).val at heq'
    omega
  · simp only [if_neg hv, if_pos hw]
    intro heq
    have heq' := congrArg Fin.val heq
    have hlt := (p v).isLt
    change (p v).val = 2 at heq'
    omega
  · simp only [if_neg hv, if_neg hw]
    intro heq
    have hp : p v = p w := Fin.castSucc_inj.mp heq
    exact (hcover hadj hp).elim hv hw

/-- The cut-support lemma. Its contrapositive is a necessary condition for
non-three-colourability, not a sufficient condition. -/
theorem colorable_three_of_bipartite_badSupport {V : Type u} (G : SimpleGraph V)
    (p : V → Fin 2) (h : (G.induce (badSupport G p)).Colorable 2) :
    G.Colorable 3 := by
  classical
  obtain ⟨c⟩ := h
  let S : Set V := {v | ∃ hv : v ∈ badSupport G p, c ⟨v, hv⟩ = 0}
  apply colorable_three_of_independent_cover G p S
  · intro v w hadj hv hw
    obtain ⟨hv, hcv⟩ := hv
    obtain ⟨hw, hcw⟩ := hw
    have hn : c ⟨v, hv⟩ ≠ c ⟨w, hw⟩ := c.valid hadj
    exact hn (hcv.trans hcw.symm)
  · intro v w hadj hp
    have hv : v ∈ badSupport G p := ⟨w, hadj, hp⟩
    have hw : w ∈ badSupport G p := ⟨v, hadj.symm, hp.symm⟩
    have hn : c ⟨v, hv⟩ ≠ c ⟨w, hw⟩ := c.valid hadj
    by_cases hc : c ⟨v, hv⟩ = 0
    · exact Or.inl ⟨hv, hc⟩
    · right
      refine ⟨hw, ?_⟩
      have hvlt := (c ⟨v, hv⟩).isLt
      have hwlt := (c ⟨w, hw⟩).isLt
      apply Fin.eq_of_val_eq
      have hcv : (c ⟨v, hv⟩).val ≠ 0 := by
        intro hh
        apply hc
        exact Fin.eq_of_val_eq hh
      have hneq : (c ⟨v, hv⟩).val ≠ (c ⟨w, hw⟩).val := by
        intro hh
        exact hn (Fin.eq_of_val_eq hh)
      simp only [Fin.val_zero]
      omega

end Erdos74Analysis
