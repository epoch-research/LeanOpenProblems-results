import Submission.Work

/-!
Independent extension and recoloring. This file does not settle Erdős Problem 595.
It records why adding even all allowable new apices simultaneously cannot destroy
an existing countable triangle-free edge cover when those apices are independent.
-/

open SimpleGraph Set
open Erdos595Work

namespace Erdos595Extension

/-- A coloring of the old edges, shifted to reserve zero for all new edges. -/
def extendedColor {V W : Type*} (c : Sym2 V → ℕ) : Sym2 (V ⊕ W) → ℕ :=
  Sym2.lift ⟨fun a b => match a, b with
    | .inl v, .inl w => c s(v, w) + 1
    | _, _ => 0, by
      intro a b
      cases a <;> cases b <;> simp [Sym2.eq_swap]⟩

/-- Any valid coloring on the old graph extends after one uniform injective
renaming of its colors, regardless of how many independent new vertices are added. -/
theorem extendedColor_valid {V W : Type*} (G : SimpleGraph (V ⊕ W))
    (c : Sym2 V → ℕ)
    (hc : ∀ a b d : V, G.Adj (.inl a) (.inl b) → G.Adj (.inl a) (.inl d) →
      G.Adj (.inl b) (.inl d) →
      ¬ (c s(a, b) = c s(a, d) ∧ c s(a, b) = c s(b, d)))
    (hW : ∀ a b : W, ¬G.Adj (.inr a) (.inr b)) :
    ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
      ¬ (extendedColor c s(a, b) = extendedColor c s(a, d) ∧
        extendedColor c s(a, b) = extendedColor c s(b, d)) := by
  intro a b d hab had hbd heq
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases d with
      | inl d =>
        apply hc a b d hab had hbd
        simpa only [extendedColor, Sym2.lift_mk, Nat.add_right_cancel_iff] using heq
      | inr d =>
        have h := heq.1
        change c s(a, b) + 1 = 0 at h
        omega
    | inr b =>
      cases d with
      | inl d =>
        have h := heq.1
        change 0 = c s(a, d) + 1 at h
        omega
      | inr d => exact hW b d hbd
  | inr a =>
    cases b with
    | inl b =>
      cases d with
      | inl d =>
        have h := heq.2
        change 0 = c s(b, d) + 1 at h
        omega
      | inr d => exact hW a d had
    | inr b => exact hW a b hab

/-- A countable triangle-free cover survives an arbitrary independent extension.
The theorem does not require a `K₄`-free hypothesis. -/
theorem countable_cover_independent_extension {V W : Type*}
    (G : SimpleGraph (V ⊕ W))
    (hc : IsCountableUnionOfTriangleFree (G.comap (Sum.inl : V → V ⊕ W)))
    (hW : ∀ a b : W, ¬G.Adj (.inr a) (.inr b)) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨c, hc⟩ := (countable_union_iff_edge_coloring _).mp hc
  apply (countable_union_iff_edge_coloring G).mpr
  exact ⟨extendedColor c, extendedColor_valid G c hc hW⟩

#print axioms extendedColor_valid
#print axioms countable_cover_independent_extension

/-- All triangle-free old neighborhoods that an independent new apex may realize. -/
abbrev Admissible {V : Type*} (G : SimpleGraph V) :=
  {S : Set V // (G.induce S).CliqueFree 3}

/-- Adjoin one independent apex for every triangle-free old neighborhood. -/
def apexFamilyGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (V ⊕ Admissible G) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr S => v ∈ S.val
    | .inr S, .inl v => v ∈ S.val
    | .inr _, .inr _ => False
  symm := by intro a b; cases a <;> cases b <;> simp_all [G.adj_comm]
  loopless := by intro a; cases a <;> simp_all

private theorem no_triangle_in_admissible {V : Type*} (G : SimpleGraph V)
    (S : Admissible G) (a b c : V) (ha : a ∈ S.val) (hb : b ∈ S.val) (hc : c ∈ S.val)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
  classical
  exact S.property _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce S.val).Adj ⟨a, ha⟩ ⟨b, hb⟩ ∧
      (G.induce S.val).Adj ⟨a, ha⟩ ⟨c, hc⟩ ∧
      (G.induce S.val).Adj ⟨b, hb⟩ ⟨c, hc⟩ from ⟨hab, hac, hbc⟩))

theorem apexFamilyGraph_cliqueFree {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (apexFamilyGraph G).CliqueFree 4 := by
  have hn : ∀ a b c d, (apexFamilyGraph G).Adj a b → (apexFamilyGraph G).Adj a c →
      (apexFamilyGraph G).Adj a d → (apexFamilyGraph G).Adj b c →
      (apexFamilyGraph G).Adj b d → (apexFamilyGraph G).Adj c d → False := by
    intro a b c d hab hac had hbc hbd hcd
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp only [apexFamilyGraph] at *
    all_goals first
      | contradiction
      | exact no_adj_common_neighbors hG hab hac hbc had hbd hcd
      | exact no_triangle_in_admissible G _ _ _ _ had hbd hcd hab hac hbc
      | exact no_triangle_in_admissible G _ _ _ _ hac hbc hcd hab had hbd
      | exact no_triangle_in_admissible G _ _ _ _ hab hbc hbd hac had hcd
      | exact no_triangle_in_admissible G _ _ _ _ hab hac had hbc hbd hcd
  classical
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have he : ∀ i j : Fin 4, i ≠ j → (apexFamilyGraph G).Adj (e i) (e j) :=
    fun i j h => e.map_rel_iff.mpr h
  exact hn (e 0) (e 1) (e 2) (e 3) (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 0 3 (by decide)) (he 1 2 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

/-- Every allowable neighborhood is realized exactly, not merely on finite subsets. -/
theorem apexFamilyGraph_extension {V : Type*} (G : SimpleGraph V)
    (S : Set V) (hS : (G.induce S).CliqueFree 3) :
    ∃ x : V ⊕ Admissible G, ∀ v : V,
      (apexFamilyGraph G).Adj x (.inl v) ↔ v ∈ S :=
  ⟨.inr ⟨S, hS⟩, fun _ => Iff.rfl⟩

/-- Simultaneously realizing all allowable old neighborhoods does not change
whether a countable triangle-free edge cover exists. -/
theorem countable_cover_apexFamilyGraph_iff {V : Type*} (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree (apexFamilyGraph G) ↔
      IsCountableUnionOfTriangleFree G := by
  constructor
  · intro h
    let f : G →g apexFamilyGraph G := ⟨Sum.inl, fun h => h⟩
    exact countable_union_of_hom f h
  · intro h
    apply countable_cover_independent_extension (apexFamilyGraph G)
    · exact h
    · intro a b h
      exact h

#print axioms apexFamilyGraph_cliqueFree
#print axioms apexFamilyGraph_extension
#print axioms countable_cover_apexFamilyGraph_iff


end Erdos595Extension
