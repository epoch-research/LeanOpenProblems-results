import FormalConjecturesUtil
import Submission.CompactThreeRates

/-! Component-wise rational growth thresholds, without transferring exact
asymptotics from a disjoint union to one component. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713ComponentRates
open Erdos713Rate
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
theorem rate_of_fibres {W : Type u} [Fintype W] {I : Type v}
    (G : SimpleGraph W) (χ : W → I)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v)
    (hR : ∀ i, ∃ r : ℚ, HasRate (G.induce {w | χ w = i}) (r : ℝ)) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (χ : W → I),
      (∀ u v, G.Adj u v → χ u = χ v) →
      (∀ i, ∃ r : ℚ, HasRate (G.induce {w | χ w = i}) (r : ℝ)) →
        ∃ r : ℚ, HasRate G (r : ℝ) from hP _ W rfl G χ hχ hR
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G χ hχ hR
    by_cases hne : Nonempty W
    swap
    · letI : IsEmpty W := not_nonempty_iff.mp hne
      exact ⟨1,by simpa using forest_rate G (by intro v; exact isEmptyElim v)⟩
    let w : W := hne.some
    let i : I := χ w
    let S : Set W := {v | χ v = i}
    have hsmall : Fintype.card ↥(Sᶜ) < k :=
      (Fintype.card_subtype_lt (x := w) (by simp [S,i])).trans_eq hW
    have hχ' : ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Adj u v → χ u.val = χ v.val := by
      intro u v huv
      exact hχ _ _ huv
    have hR' : ∀ j, ∃ r : ℚ,
        HasRate ((G.induce Sᶜ).induce {v : ↥(Sᶜ) | χ v.val = j}) (r : ℝ) := by
      intro j
      by_cases hj : j = i
      · subst j
        letI : IsEmpty {v : ↥(Sᶜ) // χ v.val = i} := ⟨fun v => v.val.prop v.prop⟩
        exact ⟨1,by simpa using forest_rate _ (by intro v; exact isEmptyElim v)⟩
      · obtain ⟨r,hr⟩ := hR j
        exact ⟨r,iso_rate (fibreComplementIso G χ hj) hr⟩
    obtain ⟨r₂,hSc⟩ := ih _ hsmall _ rfl (G.induce Sᶜ) (fun v => χ v.val) hχ' hR'
    obtain ⟨r₁,hr₁⟩ := hR i
    have he : G.induce S ⊕g G.induce Sᶜ ≃g G := splitIso G S (by
      intro u v huv
      change χ u = i ↔ χ v = i
      rw [hχ u v huv])
    refine ⟨max r₁ r₂,?_⟩
    simpa only [Rat.cast_max] using iso_rate he.symm (sum_rate hr₁ hSc)

open scoped Classical in
theorem rate_of_components {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hR : ∀ C : G.ConnectedComponent, ∃ r : ℚ, HasRate C.toSimpleGraph (r : ℝ)) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  apply rate_of_fibres G G.connectedComponentMk
  · intro u v huv
    exact ConnectedComponent.connectedComponentMk_eq_of_adj huv
  · intro C
    exact hR C

open scoped Classical in
theorem rate_of_small_component_bipartitions {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hS : ∀ C : G.ConnectedComponent, ∃ S : Set C,
      C.toSimpleGraph.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  apply rate_of_components G
  intro C
  obtain ⟨S,hB,hcard⟩ := hS C
  exact Erdos713ThreeSide.rate_of_small_bipartition C.toSimpleGraph S hB hcard

open scoped Classical in
theorem rate_of_small_components {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hB : G.IsBipartite)
    (hcard : ∀ C : G.ConnectedComponent, Nat.card C ≤ 7) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  apply rate_of_components G
  intro C
  exact Erdos713ThreeSide.rate_of_card_le_seven C.toSimpleGraph
    (hB.of_hom C.toSimpleGraph_hom) (by simpa only [Nat.card_eq_fintype_card] using hcard C)

open scoped Classical in
theorem rational_of_component_rates {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hR : ∀ C : G.ConnectedComponent, ∃ r : ℚ, HasRate C.toSimpleGraph (r : ℝ))
    {a c : ℝ} (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := rate_of_components G hR
  exact ⟨r,(exponent_eq hr ha hc h).symm⟩

open scoped Classical in
theorem rational_of_small_component_bipartitions {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hS : ∀ C : G.ConnectedComponent, ∃ S : Set C,
      C.toSimpleGraph.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3)
    {a c : ℝ} (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := rate_of_small_component_bipartitions G hS
  exact ⟨r,(exponent_eq hr ha hc h).symm⟩

#print axioms rate_of_components
#print axioms rational_of_small_component_bipartitions
end Erdos713ComponentRates
