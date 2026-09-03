import FormalConjecturesUtil
import Submission.ThetaRowTruncation
import Submission.ThetaAnchorBudget

/-! Row restriction with a controlled light-pair budget, and a two-sided
row-degree normalization. No vanishing or rationality theorem is assumed. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRowRestriction
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
open Erdos713ThetaAnchorBudget Erdos713ThetaRowTruncation
universe u v
variable {A : Type u} {B : Type v}
set_option maxHeartbeats 2000000

def restrict (R : A → B → Prop) (S : Finset A) : S → B → Prop := fun a b => R a.val b

lemma restrict_row [Fintype B] (R : A → B → Prop) (S : Finset A) (a : S) :
    row (restrict R S) a = row R a.val := rfl

lemma restrict_no_theta {R : A → B → Prop} (hf : ¬ HasTheta R) (S : Finset A) :
    ¬ HasTheta (restrict R S) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  exact hf ⟨fun i => (a i).val,b,Subtype.val_injective.comp ha,hb,
    h00,h10,h01,h11,h02,h22,h13,h23⟩

lemma column_card_le_of_injective {C : Type*} [Finite A] [Finite C]
    (R : A → B → Prop) (f : C → A) (hf : Function.Injective f) (b : B) :
    Nat.card {a : C // R (f a) b} ≤ Nat.card {a : A // R a b} := by
  let g : {a : C // R (f a) b} → {a : A // R a b} := fun a => ⟨f a.val,a.property⟩
  exact Nat.card_le_card_of_injective g (fun a c h =>
    Subtype.ext (hf (congrArg Subtype.val h)))

lemma restrict_codegree [Fintype A] [Fintype B] (R : A → B → Prop)
    (S : Finset A) (p : B × B) :
    codegree (restrict R S) p.1 p.2 = (commonRows R S p).card := by
  have he := Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun a : A => a ∈ S) (fun a => R a p.1 ∧ R a p.2))
  have hfilter : (univ : Finset A).filter (fun a => a ∈ S ∧ R a p.1 ∧ R a p.2) =
      S.filter (fun a => R a p.1 ∧ R a p.2) := by
    ext a
    simp
  simpa only [codegree,restrict,Nat.card_eq_fintype_card,Fintype.card_subtype,
    commonRows,hfilter] using he

/-- A newly light pair has lost a supporting row. Diagonal pairs are
included, which is why the cost is the sum of squared row degrees. -/
theorem light_restrict_le [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A) :
    lightCount (restrict R S) ≤ lightCount R +
      ∑ a ∈ univ \ S, (row R a).card^2 := by
  have hsub : lightSet (restrict R S) ⊆
      lightSet R ∪ (univ \ S).biUnion (fun a => row R a ×ˢ row R a) := by
    intro p hp
    by_cases hl : codegree R p.1 p.2 ≤ 2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hl⟩)
    · have hnew : codegree (restrict R S) p.1 p.2 ≤ 2 := (mem_filter.mp hp).2
      rw [restrict_codegree] at hnew
      have hs := commonRows_split R S p
      have hpos : 0 < (commonRows R (univ \ S) p).card := by omega
      obtain ⟨a,ha⟩ := card_pos.mp hpos
      have ha' := mem_filter.mp ha
      exact mem_union_right _ (mem_biUnion.mpr ⟨a,ha'.1,
        mem_product.mpr ⟨(mem_row R _ _).mpr ha'.2.1,(mem_row R _ _).mpr ha'.2.2⟩⟩)
  rw [← lightSet_card,← lightSet_card R]
  calc
    _ ≤ (lightSet R ∪ (univ \ S).biUnion (fun a => row R a ×ˢ row R a)).card :=
      card_le_card hsub
    _ ≤ (lightSet R).card + ((univ \ S).biUnion (fun a => row R a ×ˢ row R a)).card :=
      card_union_le _ _
    _ ≤ (lightSet R).card + ∑ a ∈ univ \ S, (row R a ×ˢ row R a).card :=
      Nat.add_le_add_left card_biUnion_le _
    _ = _ := by simp only [card_product,pow_two]

lemma restrict_incidence_sum [Fintype B] (R : A → B → Prop) (S : Finset A) :
    (∑ a : S, (row (restrict R S) a).card) = ∑ a ∈ S, (row R a).card := by
  simpa only [restrict_row] using (sum_coe_sort S (fun a => (row R a).card))

/-- Removing rows above the packing scale loses at most t incidences and
increases the light-pair budget by at most a factor of five. -/
theorem truncate_high [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r : ℕ) (hr : 4 ≤ r) (hmin : ∀ a, r ≤ (row R a).card) :
    ∃ S : Finset A,
      (∀ a ∈ S, (row R a).card^2*(r-3) < 12*Fintype.card B) ∧
      (∑ a : A, (row R a).card) ≤
        (∑ a : S, (row (restrict R S) a).card) + lightCount R ∧
      lightCount (restrict R S) ≤ 5*lightCount R := by
  let S := (univ : Finset A).filter (fun a =>
    (row R a).card^2*(r-3) < 12*Fintype.card B)
  have hbad (a : A) (ha : a ∈ univ \ S) :
      12*Fintype.card B ≤ (row R a).card^2*(r-3) := by
    have hn := (mem_sdiff.mp ha).2
    simpa [S] using hn
  have hi := large_row_incidences_at hf r hr hmin (univ \ S) hbad
  have hs := large_row_squares_at hf r hr hmin (univ \ S) hbad
  refine ⟨S,fun a ha => (mem_filter.mp ha).2,?_,?_⟩
  · rw [restrict_incidence_sum]
    have he := sum_add_sum_compl (s := S) (f := fun a => (row R a).card)
    change (∑ a ∈ S, (row R a).card) + (∑ a ∈ univ \ S, (row R a).card) =
      (∑ a : A, (row R a).card) at he
    omega
  · have hl := light_restrict_le R S
    omega

/-- The complete normalization keeps the columns unchanged and only
restricts rows. In particular any maximum-column-degree cap is inherited.
The stated losses use the original m and t. -/
theorem normalize_rows [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r : ℕ) (hr : 4 ≤ r) :
    ∃ (C : Type u) (_ : Fintype C) (f : C → A), Function.Injective f ∧
      Fintype.card C ≤ Fintype.card A ∧
      (∀ a : C, r ≤ (row R (f a)).card ∧
        (row R (f a)).card^2*(r-3) < 12*Fintype.card B) ∧
      ¬ HasTheta (fun a : C => R (f a)) ∧
      (∑ a : A, (row R a).card) ≤
        (∑ a : C, (row R (f a)).card) + lightCount R +
          (r^2+r)*Fintype.card A ∧
      lightCount (fun a : C => R (f a)) ≤
        5*(lightCount R+r^2*Fintype.card A) := by
  let S := (univ : Finset A).filter (fun a => r ≤ (row R a).card)
  let Q := restrict R S
  have hQ := restrict_no_theta hf S
  have hmin (a : S) : r ≤ (row Q a).card := (mem_filter.mp a.property).2
  have hlow (a : A) (ha : a ∈ univ \ S) : (row R a).card ≤ r := by
    have hn := (mem_sdiff.mp ha).2
    have hh : ¬ r ≤ (row R a).card := by simpa [S] using hn
    omega
  have hinc : (∑ a ∈ univ \ S, (row R a).card) ≤ r*Fintype.card A := by
    calc
      _ ≤ ∑ _a ∈ univ \ S, r := sum_le_sum (fun a ha => hlow a ha)
      _ = r*(univ \ S).card := by simp [Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (card_le_univ _)
  have hsquare : (∑ a ∈ univ \ S, (row R a).card^2) ≤ r^2*Fintype.card A := by
    calc
      _ ≤ ∑ _a ∈ univ \ S, r^2 := sum_le_sum (fun a ha => Nat.pow_le_pow_left (hlow a ha) 2)
      _ = r^2*(univ \ S).card := by simp [Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (card_le_univ _)
  have hlight : lightCount Q ≤ lightCount R+r^2*Fintype.card A :=
    (light_restrict_le R S).trans (Nat.add_le_add_left hsquare _)
  have he : (∑ a : A, (row R a).card) ≤
      (∑ a : S, (row Q a).card)+r*Fintype.card A := by
    rw [restrict_incidence_sum]
    have hh := sum_add_sum_compl (s := S) (f := fun a => (row R a).card)
    change (∑ a ∈ S, (row R a).card) + (∑ a ∈ univ \ S, (row R a).card) =
      (∑ a : A, (row R a).card) at hh
    omega
  obtain ⟨T,hT,hE,hL⟩ := truncate_high hQ r hr hmin
  let f : T → A := fun a => a.val.val
  have hinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  refine ⟨T,inferInstance,f,hinj,Fintype.card_le_of_injective f hinj,?_,?_,?_,?_⟩
  · intro a
    exact ⟨hmin a.val,hT a.val a.property⟩
  · exact restrict_no_theta hQ T
  · have htotal := he.trans (Nat.add_le_add_right hE (r*Fintype.card A))
    change (∑ a : A, (row R a).card) ≤ (∑ a : T, (row R (f a)).card) +
      lightCount Q + r*Fintype.card A at htotal
    nlinarith only [htotal,hlight]
  · exact hL.trans (Nat.mul_le_mul_left 5 hlight)

#print axioms column_card_le_of_injective
#print axioms light_restrict_le
#print axioms truncate_high
#print axioms normalize_rows
end Erdos713ThetaRowRestriction
