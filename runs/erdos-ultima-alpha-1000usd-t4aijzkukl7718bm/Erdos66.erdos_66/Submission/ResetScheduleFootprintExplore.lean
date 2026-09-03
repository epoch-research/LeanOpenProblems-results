import Submission.CentralEndpointResetExplore
import Submission.CompactnessExplore

/-! The cumulative footprint of a sequence of local edits, and its exact
role in a limiting representation estimate. The small-footprint hypothesis
is NOT inferred from bounds on individual triple intersections. -/
namespace Erdos66ResetScheduleFootprint
open Filter AdditiveCombinatorics Erdos66CentralEndpointReset
  Erdos66CentralTripleDeletion Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma localized_edit_bound_below (A B C : Set ℕ) (E : Finset ℕ) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (z : ℕ) (hagree : ∀ a ≤ z, a∉E → (a∈B ↔ a∈C)) :
    |(sumRep C z:ℝ)-sumRep B z| ≤ 2*((hits A E z).card:ℝ) := by
  let C' : Set ℕ := {a | (a ≤ z ∧ a∈C) ∨ (z<a ∧ a∈B)}
  have hC'A : C' ⊆ A := by
    intro a ha
    rcases ha with ha | ha
    · exact hCA ha.2
    · exact hBA ha.2
  have he : sumRep C' z=sumRep C z := by
    apply sumRep_congr_below
    intro a ha
    simp only [C',Set.mem_setOf_eq,ha,true_and,not_lt.mpr ha,false_and,or_false]
  rw [←he]
  apply localized_edit_bound A B C' E hBA hC'A
  intro a ha
  by_cases haz : a ≤ z
  · simpa only [C',Set.mem_setOf_eq,haz,true_and,not_lt.mpr haz,false_and,or_false] using hagree a haz ha
  · simp only [C',Set.mem_setOf_eq,haz,false_and,lt_of_not_ge haz,true_and,false_or]

noncomputable def limitSet (B : ℕ → Set ℕ) : Set ℕ :=
  {a | ∃ s, ∀ t≥s, a∈B t}

noncomputable def tailFootprint (E : ℕ → Finset ℕ) (s z : ℕ) : Finset ℕ :=
  (Finset.range (z+1)).filter (fun a ↦ ∃ t≥s, a∈E t)

lemma mem_tailFootprint {E : ℕ → Finset ℕ} {s z a : ℕ} :
    a∈tailFootprint E s z ↔ a ≤ z ∧ ∃ t≥s, a∈E t := by
  simp only [tailFootprint,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

lemma membership_stable (B : ℕ → Set ℕ) (E : ℕ → Finset ℕ)
    (hstep : ∀ t a, a∉E t → (a∈B t ↔ a∈B (t+1)))
    (a s : ℕ) (htail : ∀ t≥s, a∉E t) : ∀ t≥s, a∈B t ↔ a∈B s := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => exact (hstep t a (htail t ht)).symm.trans ih

lemma limitSet_mem_of_stable (B : ℕ → Set ℕ) (E : ℕ → Finset ℕ)
    (hstep : ∀ t a, a∉E t → (a∈B t ↔ a∈B (t+1)))
    (a s : ℕ) (htail : ∀ t≥s, a∉E t) : a∈limitSet B ↔ a∈B s := by
  constructor
  · rintro ⟨u,hu⟩
    exact (membership_stable B E hstep a s htail (max s u) (le_max_left _ _)).mp
      (hu (max s u) (le_max_right _ _))
  · intro ha
    exact ⟨s,fun t ht ↦ (membership_stable B E hstep a s htail t ht).mpr ha⟩

lemma limitSet_subset (A : Set ℕ) (B : ℕ → Set ℕ) (hB : ∀ t, B t ⊆ A) : limitSet B ⊆ A := by
  rintro a ⟨s,hs⟩
  exact hB s (hs s le_rfl)

/-- No coordinate-stabilization assumption is needed for this bound. Outside
the future footprint, membership is constant; inside it, the bound charges
all possibly affected host representations, counting each endpoint once. -/
lemma limitSet_change_bound (A : Set ℕ) (B : ℕ → Set ℕ) (E : ℕ → Finset ℕ)
    (hB : ∀ t, B t ⊆ A)
    (hstep : ∀ t a, a∉E t → (a∈B t ↔ a∈B (t+1))) (s z : ℕ) :
    |(sumRep (limitSet B) z:ℝ)-sumRep (B s) z| ≤
      2*((hits A (tailFootprint E s z) z).card:ℝ) := by
  apply localized_edit_bound_below A (B s) (limitSet B) (tailFootprint E s z)
    (hB s) (limitSet_subset A B hB) z
  intro a haz ha
  apply (limitSet_mem_of_stable B E hstep a s ?_).symm
  intro t ht hat
  exact ha (mem_tailFootprint.mpr ⟨haz,t,ht,hat⟩)

lemma eventually_constant_coordinate (B : ℕ → Set ℕ) (E : ℕ → Finset ℕ)
    (hstep : ∀ t a, a∉E t → (a∈B t ↔ a∈B (t+1)))
    (hescape : ∀ a, ∃ s, ∀ t≥s, a∉E t) (a : ℕ) :
    ∀ᶠ t : ℕ in atTop, a∈B t ↔ a∈limitSet B := by
  obtain ⟨s,hs⟩ := hescape a
  filter_upwards [eventually_ge_atTop s] with t ht
  exact (membership_stable B E hstep a s hs t ht).trans
    (limitSet_mem_of_stable B E hstep a s hs).symm

lemma central_support_escape (A : Set ℕ) (d : ℕ) (hd : 0<d) (a : ℕ) :
    ∃ s, ∀ t≥s, a∉endpoints A (t/d^2) t := by
  refine ⟨d^2*(a+1),?_⟩
  intro t ht ha
  have hpos : 0<d^2 := pow_pos hd _
  have hdiv : a+1 ≤ t/d^2 := (Nat.le_div_iff_mul_le hpos).mpr (by simpa only [Nat.mul_comm] using ht)
  have hmem := (mem_endpoints.mp ha).2.1
  omega

end Erdos66ResetScheduleFootprint
