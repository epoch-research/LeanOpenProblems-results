import Submission.CoreUnionOvercount
import Submission.BooleanCoreFootprint

/-! Exact compression of the large minimal-core overcount example. The union
of all its core events equals the union of just two events. This is a test of
an overlap-aware approach, not an unrestricted odd-covering obstruction. -/
namespace Erdos7CoreFootprintCompression
open scoped BigOperators
open Erdos7ManyBooleanCores Erdos7CoreUnionOvercount
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
attribute [local irreducible] allCores

lemma pair_eq_special (i : Coord) :
    Erdos7BooleanCoreFootprint.pair Branch encode i = (special i).val := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨v,rfl⟩ := (Erdos7BooleanCoreFootprint.mem_pair Branch encode i x).mp hx
    exact encode_mem_special i v
  · rw [Erdos7BooleanCoreFootprint.pair_card Branch encode encode_injective]
    exact (Finset.mem_powersetCard.mp (special i).property).2.le

/-- The event of a core depends only on its coordinate footprint. -/
theorem event_iff_footprint (s : Finset Clause) (hs : s ∈ allCores) (z : Sample) :
    MinimalCoreEvent s z ↔ ∀ i ∈ s.biUnion support, (z i).val = (special i).val := by
  have hh := many_minimal_cores.2.2.2 s hs
  have h := Erdos7BooleanCoreFootprint.minimal_event_iff Branch support bit s hh.1 hh.2
    encode encode_injective (fun i => (z i).val)
    (fun i => (Finset.mem_powersetCard.mp (z i).property).2)
  simpa only [Erdos7BooleanCoreFootprint.MinimalEvent, MinimalCoreEvent,
    CoreEvent, pair_eq_special] using h

lemma base_coordinate_used : ∀ c : Fin 4, ∃ j : Fin 6, c ∈ baseSupport j := by
  decide +kernel

lemma used_left (f : Old → Fin 2) (i : Fin 3) (c : Fin 4) :
    Sum.inl (i,c) ∈ (core f).biUnion support := by
  obtain ⟨t,ht⟩ := base_coordinate_used c
  let j : Old := fun _ => t
  exact Finset.mem_biUnion.mpr ⟨(j,f j,0),(mem_core f _).mpr rfl,
    (mem_support_left _ _ _).mpr ht⟩

lemma used_right (f : Old → Fin 2) (b : Fin 2) (c : Fin 4) :
    Sum.inr (b,c) ∈ (core f).biUnion support ↔ ∃ j : Old, f j=b := by
  constructor
  · intro h
    obtain ⟨k,hk,hmem⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hb,_⟩ := (mem_support_right _ _ _).mp hmem
    exact ⟨k.1,((mem_core f _).mp hk).symm.trans hb.symm⟩
  · rintro ⟨j,hj⟩
    obtain ⟨t,ht⟩ := base_coordinate_used c
    refine Finset.mem_biUnion.mpr ⟨(j,b,t),(mem_core f _).mpr hj.symm,?_⟩
    exact (mem_support_right _ _ _).mpr ⟨rfl,ht⟩

lemma constant_footprint_subset (f : Old → Fin 2) (j : Old) :
    (core (fun _ => f j)).biUnion support ⊆ (core f).biUnion support := by
  rintro (⟨i,c⟩|⟨b,c⟩) h
  · exact used_left f i c
  · obtain ⟨_,hb⟩ := (used_right (fun _ => f j) b c).mp h
    exact (used_right f b c).mpr ⟨j,hb⟩

lemma image_univ_mem {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (a : A) :
    f a ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩

lemma mem_image_univ_iff {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (b : B) :
    b ∈ Finset.univ.image f ↔ ∃ a, b=f a := by
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  exact exists_congr fun _ => eq_comm

lemma core_mem (f : Old → Fin 2) : core f ∈ allCores := by
  unfold allCores
  exact image_univ_mem core f

lemma exists_core_of_mem (s : Finset Clause) (hs : s ∈ allCores) : ∃ f, s=core f := by
  unfold allCores at hs
  exact (mem_image_univ_iff core s).mp (show s ∈ Finset.univ.image core from hs)

/-- Every event among 2^216 cores is contained in the event of one of the two
constant gadget choices. Thus its union has only two maximal events. -/
theorem union_eq_two (z : Sample) :
    (∃ s ∈ allCores, MinimalCoreEvent s z) ↔
      MinimalCoreEvent (core (fun _ => 0)) z ∨ MinimalCoreEvent (core (fun _ => 1)) z := by
  constructor
  · rintro ⟨s,hs,hz⟩
    obtain ⟨f,rfl⟩ := exists_core_of_mem s hs
    let j : Old := fun _ => 0
    have hfoot := (event_iff_footprint (core f) hs z).mp hz
    have hc : MinimalCoreEvent (core (fun _ => f j)) z :=
      (event_iff_footprint _ (core_mem _) z).mpr
        (fun i hi => hfoot i (constant_footprint_subset f j hi))
    have hf : f j = 0 ∨ f j = 1 := by have := (f j).isLt; omega
    rcases hf with h | h
    · left; simpa only [h] using hc
    · right; simpa only [h] using hc
  · rintro (h|h)
    · exact ⟨_,core_mem _,h⟩
    · exact ⟨_,core_mem _,h⟩

/-- Exact single-coordinate probability in a finite product. The proof is
abstract in the types, so no huge product enumeration is triggered. -/
lemma coordinate_fraction {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (i : I) (a : A i) :
    ((Finset.univ.filter (fun x : (j : I) → A j => x i=a)).card : ℚ) /
      Fintype.card ((j : I) → A j) = 1/(Fintype.card (A i) : ℚ) := by
  classical
  have hh := Fintype.card_filter_piFinset_eq_of_mem (fun j : I => (Finset.univ : Finset (A j)))
    i (Finset.mem_univ a)
  simp only [Fintype.piFinset_univ,Finset.card_univ] at hh
  rw [hh,Fintype.card_pi,Nat.cast_prod,Nat.cast_prod]
  have he := Finset.mul_prod_erase (Finset.univ : Finset I) (fun j => (Fintype.card (A j) : ℚ))
    (Finset.mem_univ i)
  rw [← he]
  have hi : (Fintype.card (A i) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (Fintype.card_pos (α := A i)))
  have hrest : (∏ j ∈ (Finset.univ : Finset I).erase i, (Fintype.card (A j) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by exact_mod_cast (ne_of_gt (Fintype.card_pos (α := A j))))
  field_simp

lemma probability_mono {X : Type*} [Fintype X] (P Q : X → Prop)
    (h : ∀ x, P x → Q x) :
    letI : DecidablePred P := Classical.decPred _
    letI : DecidablePred Q := Classical.decPred _
    ((Finset.univ.filter P).card : ℚ)/Fintype.card X ≤
      ((Finset.univ.filter Q).card : ℚ)/Fintype.card X := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hh : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,h x (Finset.mem_filter.mp hx).2⟩
  exact_mod_cast Finset.card_le_card hh

/-- In contrast to the raw sum >1, the ACTUAL union probability is at most
1/45. Already the first prime must choose one specified pair of its ten nonzero
branches. This bound uses the exact event union, not separate core estimates. -/
theorem union_probability_le :
    letI : DecidablePred (fun z : Sample => ∃ s ∈ allCores, MinimalCoreEvent s z) := Classical.decPred _
    ((Finset.univ.filter (fun z : Sample => ∃ s ∈ allCores, MinimalCoreEvent s z)).card : ℚ) /
      Fintype.card Sample ≤ 1/45 := by
  classical
  let i : Coord := .inl (0,0)
  letI (i : Coord) : Nonempty (PairChoice i) := ⟨special i⟩
  have h := probability_mono (fun z : Sample => ∃ s ∈ allCores, MinimalCoreEvent s z)
    (fun z => z i=special i) (fun z hz => by
      obtain ⟨s,hs,hz⟩ := hz
      obtain ⟨f,rfl⟩ := exists_core_of_mem s hs
      apply Subtype.ext
      exact (event_iff_footprint _ hs z).mp hz i (used_left f 0 0))
  have he := coordinate_fraction (A := PairChoice) i (special i)
  have hi : Fintype.card (PairChoice i) = 45 := by
    rw [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
    decide +kernel
  rw [Finset.filter_congr_decidable (Finset.univ : Finset Sample)
    (fun z => z i=special i) (Classical.decPred _)] at h
  rw [he,hi] at h
  exact h

#print axioms event_iff_footprint
#print axioms union_eq_two
#print axioms union_probability_le
end Erdos7CoreFootprintCompression
