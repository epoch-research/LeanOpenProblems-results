import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713Components
open Erdos713Reduction
universe u v

noncomputable def splitIso {W : Type*} (G : SimpleGraph W) (S : Set W)
    (hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S)) :
    G.induce S ⊕g G.induce Sᶜ ≃g G := by
  classical
  refine ⟨Equiv.Set.sumCompl S, ?_⟩
  rintro (u | u) (v | v)
  · rfl
  · change G.Adj u.val v.val ↔ (false = true)
    simp only [Bool.false_eq_true, iff_false]
    exact fun huv => v.prop ((hS _ _ huv).mp u.prop)
  · change G.Adj u.val v.val ↔ (false = true)
    simp only [Bool.false_eq_true, iff_false]
    exact fun huv => u.prop ((hS _ _ huv).mpr v.prop)
  · rfl

noncomputable def fibreComplementIso {W I : Type*} (G : SimpleGraph W)
    (χ : W → I) {i j : I} (hij : j ≠ i) :
    (G.induce {w | χ w ≠ i}).induce {w | χ w.val = j} ≃g G.induce {w | χ w = j} := by
  let e : {w : {w // χ w ≠ i} // χ w.val = j} ≃ {w // χ w = j} :=
    { toFun := fun w => ⟨w.val.val, w.prop⟩
      invFun := fun w => ⟨⟨w.val, by simpa only [w.prop] using hij⟩, w.prop⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }
  exact ⟨e, Iff.rfl⟩

open scoped Classical in
theorem reduces_of_fibres {W : Type u} [Fintype W] {I : Type v}
    (G : SimpleGraph W) (χ : W → I)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v)
    (hR : ∀ i, Reduces {w // χ w = i} (G.induce {w | χ w = i})) : Reduces W G := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (χ : W → I),
      (∀ u v, G.Adj u v → χ u = χ v) →
      (∀ i, Reduces {w // χ w = i} (G.induce {w | χ w = i})) → Reduces W G from
    hP _ W rfl G χ hχ hR
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G χ hχ hR
    by_cases hne : Nonempty W
    swap
    · letI : IsEmpty W := not_nonempty_iff.mp hne
      exact .forest (by intro v; exact isEmptyElim v)
    let w : W := hne.some
    let i : I := χ w
    let S : Set W := {v | χ v = i}
    have hsmall : Fintype.card ↥(Sᶜ) < k :=
      (Fintype.card_subtype_lt (x := w) (by simp [S, i])).trans_eq hW
    have hχ' : ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Adj u v → χ u.val = χ v.val := by
      intro u v huv
      exact hχ _ _ huv
    have hR' : ∀ j, Reduces {v : ↥(Sᶜ) // χ v.val = j}
        ((G.induce Sᶜ).induce {v : ↥(Sᶜ) | χ v.val = j}) := by
      intro j
      by_cases hj : j = i
      · subst j
        letI : IsEmpty {v : ↥(Sᶜ) // χ v.val = i} := ⟨fun v => v.val.prop v.prop⟩
        exact .forest (by intro v; exact isEmptyElim v)
      · exact .iso (fibreComplementIso G χ hj) (hR j)
    have hSc := ih _ hsmall _ rfl (G.induce Sᶜ) (fun v => χ v.val) hχ' hR'
    apply Reduces.iso (splitIso G S ?_).symm (.sum (hR i) hSc)
    intro u v huv
    change χ u = i ↔ χ v = i
    rw [hχ u v huv]

open scoped Classical in
theorem reduces_of_components {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hR : ∀ C : G.ConnectedComponent, Reduces C C.toSimpleGraph) : Reduces W G := by
  classical
  apply reduces_of_fibres G G.connectedComponentMk
  · intro u v huv
    exact ConnectedComponent.connectedComponentMk_eq_of_adj huv
  · intro C
    exact hR C

open scoped Classical in
theorem reduces_of_small_components {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite)
    (hcard : ∀ C : G.ConnectedComponent, Nat.card C ≤ 7) : Reduces W G := by
  classical
  apply reduces_of_components G
  intro C
  apply Erdos713Structural.reduces_of_card_le_seven C.toSimpleGraph
  · exact hB.of_hom C.toSimpleGraph_hom
  · simpa only [Nat.card_eq_fintype_card] using hcard C

open scoped Classical in
theorem reduces_of_small_component_bipartitions {W : Type u} [Fintype W]
    (G : SimpleGraph W)
    (hS : ∀ C : G.ConnectedComponent, ∃ S : Set C,
      C.toSimpleGraph.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3) : Reduces W G := by
  classical
  apply reduces_of_components G
  intro C
  obtain ⟨S, hB, hcard⟩ := hS C
  exact Erdos713Structural.reduces_of_small_bipartition C.toSimpleGraph S hB hcard

open scoped Classical in
theorem exists_large_component_of_not_reduces {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite) (hR : ¬Reduces W G) :
    ∃ C : G.ConnectedComponent, ¬Reduces C C.toSimpleGraph ∧ 8 ≤ Nat.card C ∧
      ∀ S : Set C, C.toSimpleGraph.IsBipartiteWith S Sᶜ → 4 ≤ Nat.card S := by
  classical
  have hn : ¬∀ C : G.ConnectedComponent, Reduces C C.toSimpleGraph :=
    fun h => hR (reduces_of_components G h)
  push_neg at hn
  obtain ⟨C, hC⟩ := hn
  refine ⟨C, hC, ?_, ?_⟩
  · by_contra hh
    have hc : Fintype.card C ≤ 7 := by
      simp only [Nat.card_eq_fintype_card] at hh
      omega
    exact hC (Erdos713Structural.reduces_of_card_le_seven C.toSimpleGraph
      (hB.of_hom C.toSimpleGraph_hom) hc)
  · intro S hS
    by_contra hh
    exact hC (Erdos713Structural.reduces_of_small_bipartition C.toSimpleGraph S hS (by omega))

#print axioms reduces_of_fibres
#print axioms reduces_of_components
#print axioms reduces_of_small_components

#print axioms reduces_of_small_component_bipartitions
#print axioms exists_large_component_of_not_reduces

end Erdos713Components
