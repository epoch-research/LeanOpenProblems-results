import Submission.LocalWindowExplore
import Submission.CountingExplore
import Submission.Explore
import Submission.CompactnessExplore

/-! Converting finite integer repairs to repairs of arbitrary natural sets. -/
namespace Erdos66NaturalRepairBridge
open AdditiveCombinatorics Erdos66OriginRepair Erdos66SymmetricSidon
  Erdos66Counting Erdos66Explore Erdos66Compactness
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def intCutoff (A : Set ℕ) (X : ℕ) : Finset ℤ :=
  (cutoff A (X + 1)).image (fun a : ℕ ↦ (a : ℤ))

lemma intCutoff_bounds {A : Set ℕ} {X : ℕ} {a : ℤ} (ha : a ∈ intCutoff A X) :
    0 ≤ a ∧ a ≤ X := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hb' := (mem_cutoff.mp hb).1
  constructor
  · positivity
  · exact_mod_cast (show b ≤ X by omega)

lemma intCutoff_toNat (A : Set ℕ) (X : ℕ) :
    (intCutoff A X).image Int.toNat = cutoff A (X + 1) := by
  simp [intCutoff, Finset.image_image, Function.comp_def]

lemma mem_intCutoff_nat {A : Set ℕ} {X a : ℕ} :
    (a : ℤ) ∈ intCutoff A X ↔ a ≤ X ∧ a ∈ A := by
  simp only [intCutoff, Finset.mem_image, mem_cutoff, Nat.cast_inj]
  constructor
  · rintro ⟨b, ⟨hb, hbA⟩, rfl⟩
    exact ⟨by omega, hbA⟩
  · rintro ⟨ha, haA⟩
    exact ⟨a, ⟨by omega, haA⟩, rfl⟩

lemma intCutoff_rep_le (A : Set ℕ) (X z : ℕ) :
    pairCount (intCutoff A X) (intCutoff A X) (z : ℤ) ≤ sumRep A z := by
  rw [pairCount_eq_sumRep_toNat _ (fun a ha ↦ (intCutoff_bounds ha).1), intCutoff_toNat]
  apply sumRep_mono
  intro a ha
  exact (mem_cutoff.mp ha).2

lemma intCutoff_uniform_bound {A : Set ℕ} {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2))
    (X : ℕ) (z : ℤ) :
    (pairCount (intCutoff A X) (intCutoff A X) z : ℝ) ≤ K + C * Real.log (2 * (X : ℝ) + 2) := by
  by_cases hz : pairCount (intCutoff A X) (intCutoff A X) z = 0
  · rw [hz, Nat.cast_zero]
    exact add_nonneg hK (mul_nonneg hC (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)))
  have hnonempty : ((intCutoff A X).filter (fun a ↦ z - a ∈ intCutoff A X)).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  obtain ⟨a, ha⟩ := hnonempty
  obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
  have ha' := intCutoff_bounds ha
  have hb' := intCutoff_bounds hb
  have hz0 : 0 ≤ z := by omega
  have hzX : z.toNat ≤ 2 * X := by omega
  have hh : (pairCount (intCutoff A X) (intCutoff A X) z : ℝ) ≤ sumRep A z.toNat := by
    have hh := intCutoff_rep_le A X z.toNat
    rw [Int.toNat_of_nonneg hz0] at hh
    exact_mod_cast hh
  apply hh.trans ((h z.toNat).trans ?_)
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hC)
  apply Real.log_le_log (by positivity)
  exact_mod_cast (show z.toNat + 2 ≤ 2 * X + 2 by omega)

lemma toNat_image_card (C : Finset ℤ) (hC : ∀ a ∈ C, 0 ≤ a) :
    (C.image Int.toNat).card = C.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have hh := congrArg (fun x : ℕ ↦ (x : ℤ)) he
  simpa only [Int.toNat_of_nonneg (hC a ha), Int.toNat_of_nonneg (hC b hb)] using hh

lemma cutoff_union_rep (A : Set ℕ) (X z : ℕ) (C : Finset ℤ)
    (hC : ∀ a ∈ C, 0 ≤ a) (hz : z ≤ X) :
    sumRep (A ∪ ((C.image Int.toNat : Finset ℕ) : Set ℕ)) z =
      pairCount (intCutoff A X ∪ C) (intCutoff A X ∪ C) (z : ℤ) := by
  have hnonneg : ∀ a ∈ intCutoff A X ∪ C, 0 ≤ a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (intCutoff_bounds ha).1
    · exact hC a ha
  rw [pairCount_eq_sumRep_toNat _ hnonneg, Finset.image_union, intCutoff_toNat, Finset.coe_union]
  apply sumRep_congr_below
  intro a ha
  simp only [Set.mem_union, Finset.mem_coe, mem_cutoff]
  have hh : a < X + 1 := by omega
  tauto

lemma cutoff_rep_eq (A : Set ℕ) (X z : ℕ) (hz : z ≤ X) :
    pairCount (intCutoff A X) (intCutoff A X) (z : ℤ) = sumRep A z := by
  rw [pairCount_eq_sumRep_toNat _ (fun a ha ↦ (intCutoff_bounds ha).1), intCutoff_toNat]
  apply sumRep_congr_below
  intro a ha
  simp only [Finset.mem_coe, mem_cutoff]
  exact and_iff_right (by omega)

lemma disjoint_of_cutoff_disjoint (A : Set ℕ) (X : ℕ) (C : Finset ℤ)
    (hC : ∀ a ∈ C, 0 ≤ a ∧ a ≤ X) (hd : Disjoint (intCutoff A X) C) :
    Disjoint A ((C.image Int.toNat : Finset ℕ) : Set ℕ) := by
  apply Set.disjoint_left.mpr
  intro a ha hc
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
  have hb' : b ∈ intCutoff A X := by
    rw [← Int.toNat_of_nonneg (hC b hb).1, mem_intCutoff_nat]
    exact ⟨by have := (hC b hb).2; omega, ha⟩
  exact Finset.disjoint_left.mp hd hb' hb

lemma sumRep_union_finset_le (A : Set ℕ) (C : Finset ℕ) (z : ℕ) :
    sumRep (A ∪ (C : Set ℕ)) z ≤ sumRep A z + 2 * C.card := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert a C ha ih =>
    rw [Finset.coe_insert, Set.union_insert, Finset.card_insert_of_notMem ha]
    have hh := sumRep_insert_le (A ∪ (C : Set ℕ)) a z
    omega

lemma union_rep_unchanged_below (A : Set ℕ) (C : Finset ℕ) (z : ℕ)
    (hC : ∀ a ∈ C, z < a) : sumRep (A ∪ (C : Set ℕ)) z = sumRep A z := by
  apply sumRep_congr_below
  intro a ha
  have hn : a ∉ C := by intro hc; have := hC a hc; omega
  simp [hn]

end Erdos66NaturalRepairBridge
