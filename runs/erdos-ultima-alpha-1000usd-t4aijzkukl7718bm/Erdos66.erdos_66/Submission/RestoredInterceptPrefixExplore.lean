import Submission.PrunedInterceptBoundsExplore

/-! Opposite labels can be pruned from the curve family and restored only
on row zero. This removes the selector's field-size exclusion condition. -/
namespace Erdos66RestoredInterceptPrefix
open Erdos66PrunedInterceptBounds Erdos66FinitePruningError
  Erdos66InterceptOppositePruning Erdos66InterceptIncidenceBudget
  Erdos66InterceptBudgetPointwise Erdos66InterceptPrefix
  Erdos66TranslatedCharacterEnergy Erdos66InheritedOriginLift
  Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2400000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def restoredPoints (U : Finset F) (a : F) : Finset (F × F) :=
  (U\pruned U a).image (fun u ↦ (u,0))

noncomputable def restored (U : Finset F) (a : F) : Finset (F × F) :=
  anchored (pruned U a) a ∪ restoredPoints U a

lemma restoredPoints_card (U : Finset F) (a : F) :
    (restoredPoints U a).card ≤ oppositeCount U a := by
  have hc : (restoredPoints U a).card ≤ (U\pruned U a).card := Finset.card_image_le
  rw [Finset.card_sdiff_of_subset (pruned_subset U a)] at hc
  have hl := pruned_card_loss U a
  omega

lemma restoredPoints_row_zero (U : Finset F) (a x : F) :
    (x,0)∈restoredPoints U a ↔ x∈U\pruned U a := by
  constructor
  · intro hx
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hx
    have hh : u=x := congrArg Prod.fst he
    simpa only [hh] using hu
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

lemma restored_row_zero (U : Finset F) (a x : F) :
    (x,0)∈restored U a ↔ x∈U := by
  rw [restored,Finset.mem_union,anchored_row_zero,restoredPoints_row_zero,Finset.mem_sdiff]
  constructor
  · rintro (h | h)
    · exact pruned_subset U a h
    · exact h.1
  · intro hx
    by_cases hh : x∈pruned U a
    · exact Or.inl hh
    · exact Or.inr ⟨hx,hh⟩

lemma restored_error (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (a : F)
    (hE : (translatedEnergy U a : ℝ) ≤ 12*(U.card : ℝ)^2) (z : F × F) :
    |(pairCount (restored U a) (restored U a) z : ℝ)-(U.card : ℝ)^2| ≤
      Real.sqrt (12*(S.card : ℝ)*(U.card : ℝ)^2)+24*U.card+
        (4*U.card+2)*oppositeCount U a+
        (correction (pruned U a) a (z-(-a,0)-(-a,0))-24*U.card : ℕ) := by
  have he := pairCount_union_abs_error (anchored (pruned U a) a) (restoredPoints U a) z
  change |(pairCount (restored U a) (restored U a) z : ℝ)-
    pairCount (anchored (pruned U a) a) (anchored (pruned U a) a) z| ≤ _ at he
  have hb := pruned_actual_bound hF U S hS a hE (z-(-a,0)-(-a,0))
  rw [←anchored_pairCount] at hb
  have hc : ((restoredPoints U a).card : ℝ) ≤ oppositeCount U a := by
    exact_mod_cast restoredPoints_card U a
  have ht := abs_sub_le (pairCount (restored U a) (restored U a) z : ℝ)
    (pairCount (anchored (pruned U a) a) (anchored (pruned U a) a) z : ℝ) ((U.card : ℝ)^2)
  nlinarith only [ht,he,hb,hc]

/-- This finite anchored construction now applies to every nonempty U in
every odd finite field. Its error bound is useful only in the displayed
quantitative regimes; this is not an infinite witness. -/
theorem exists_restored_graph (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (hU : 0 < U.card) :
    ∃ (a : F) (r : ℕ) (D : F × F → ℕ),
      (∀x : F,(x,0)∈restored U a ↔ x∈U) ∧
      Fintype.card F*r ≤ 3*U.card^2 ∧
      ∀z : F × F,
        |(pairCount (restored U a) (restored U a) z : ℝ)-(U.card : ℝ)^2| ≤
          Real.sqrt (12*(S.card : ℝ)*(U.card : ℝ)^2)+24*U.card+(4*U.card+2)*r+D z ∧
        Fintype.card F*(D z)^3 ≤ 5184*U.card^9 := by
  obtain ⟨a,hE,hB,hO⟩ := exists_energy_budget_opposites hF U hU
  let D : F × F → ℕ := fun z ↦ correction (pruned U a) a (z-(-a,0)-(-a,0))-24*U.card
  have hBn : Fintype.card F*budget U a ≤ 24*U.card^7 := by exact_mod_cast hB
  refine ⟨a,oppositeCount U a,D,restored_row_zero U a,?_,fun z ↦ ⟨?_,?_⟩⟩
  · exact_mod_cast hO
  · exact restored_error hF U S hS a hE z
  · calc
      _ ≤ Fintype.card F*(216*U.card^2*budget U a) :=
        Nat.mul_le_mul_left _ (pruned_correction_cubic hF U a _)
      _ = 216*U.card^2*(Fintype.card F*budget U a) := by ring
      _ ≤ 216*U.card^2*(24*U.card^7) := Nat.mul_le_mul_left _ hBn
      _ = _ := by ring

lemma encoded_restored_prefix (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (a : ZMod p) (n : ℕ) (hn : n<p) :
    n∈encodePlane p (restored U a) ↔ (n : ZMod p)∈U := by
  rw [encodePlane_prefix p _ n hn,restored_row_zero]

lemma encoded_restored_counts_below (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (a : ZMod p) (n : ℕ) (hn : n<p) :
    sumRep (encodePlane p (restored U a) : Set ℕ) n=
      sumRep {k : ℕ | k<p ∧ (k : ZMod p)∈U} n := by
  apply Erdos66Compactness.sumRep_congr_below
  intro k hk
  have hkp : k<p := lt_of_le_of_lt hk hn
  simpa only [Finset.mem_coe,Set.mem_setOf_eq,hkp,true_and] using encoded_restored_prefix p U a k hkp

end Erdos66RestoredInterceptPrefix
