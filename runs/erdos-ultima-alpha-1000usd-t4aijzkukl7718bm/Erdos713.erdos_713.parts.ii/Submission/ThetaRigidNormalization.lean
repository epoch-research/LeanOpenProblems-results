import FormalConjecturesUtil
import Submission.IncidencePruningBudget
import Submission.ThetaTriplePruning
import Submission.ThetaRowRestriction

/-! Pruning to pairwise row intersections of size at most two, with a
controlled light-pair budget. This does not prove SquareVanishing. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRigidNormalization
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaRowTruncation
open Erdos713IncidencePruningBudget Erdos713ThetaTriplePruning
open Erdos713ThetaRowRestriction
universe u v
variable {A : Type u} {B : Type v}
set_option maxHeartbeats 2000000

/-- Retain the clean incidences only in rows losing at most half their degree. -/
def trim [Fintype B] (R : A → B → Prop) (a : A) (x : B) : Prop :=
  clean R a x ∧ (row R a).card ≤ 2*(row (clean R) a).card

lemma trim_sub [Fintype B] (R : A → B → Prop) (a : A) (b : B) :
    trim R a b → R a b := fun h => h.1.1

lemma trim_row_good [Fintype B] (R : A → B → Prop) (a : A)
    (h : (row R a).card ≤ 2*(row (clean R) a).card) :
    row (trim R) a = row (clean R) a := by
  ext x
  simp only [mem_row,trim,h,and_true]

lemma trim_row_bad [Fintype B] (R : A → B → Prop) (a : A)
    (h : ¬ (row R a).card ≤ 2*(row (clean R) a).card) :
    row (trim R) a = ∅ := by
  ext x
  simp [mem_row,trim,h]

lemma trim_degree_alternative [Fintype B] (R : A → B → Prop) (a : A) :
    (row (trim R) a).card = 0 ∨ (row R a).card ≤ 2*(row (trim R) a).card := by
  by_cases h : (row R a).card ≤ 2*(row (clean R) a).card
  · exact Or.inr (by simpa only [trim_row_good R a h] using h)
  · exact Or.inl (by simp only [trim_row_bad R a h,card_empty])

/-- Both the incidence loss and the ordered-pair loss are paid for by
inside-row light pairs, not by weighted cross-row pairs. -/
theorem trim_row_budget [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (a : A) (ha : 4 ≤ (row R a).card) :
    (row R a).card ≤ (row (trim R) a).card+2*(insideLight R a).card ∧
      (pairLoss R (trim R) a).card ≤ 8*(insideLight R a).card := by
  let d := (row R a).card
  let b := (badColumns R a).card
  let c := (row (clean R) a).card
  let l := (insideLight R a).card
  have he : c+b=d := by
    dsimp [c,b,d]
    rw [clean_row]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have hb : b*(d-3) ≤ l := bad_columns_bound hf a
  have hd : 4 ≤ d := ha
  have hb' : b ≤ l := by
    have h := Nat.mul_le_mul_left b (show 1 ≤ d-3 by omega)
    nlinarith only [h,hb]
  have hbd : b*d ≤ 4*l := by
    have h : d ≤ 4*(d-3) := by omega
    have h' := Nat.mul_le_mul_left b h
    nlinarith only [h',hb]
  rw [pairLoss_card (trim_sub R)]
  by_cases h : d ≤ 2*c
  · have hrow : (row (trim R) a).card = c := congrArg card (trim_row_good R a h)
    change d ≤ (row (trim R) a).card+2*l ∧ d^2-(row (trim R) a).card^2 ≤ 8*l
    rw [hrow]
    constructor
    · omega
    · have hsq : c^2 ≤ d^2 := Nat.pow_le_pow_left (by omega) 2
      have hsub := Nat.sub_add_cancel hsq
      nlinarith only [he,hbd,hsub,sq_nonneg (b : ℤ)]
  · have hrow : (row (trim R) a).card = 0 := congrArg card (trim_row_bad R a h)
    change d ≤ (row (trim R) a).card+2*l ∧ d^2-(row (trim R) a).card^2 ≤ 8*l
    rw [hrow]
    constructor
    · omega
    · have hdb : d ≤ 2*b := by omega
      have hh := Nat.mul_le_mul_left d hdb
      norm_num only [zero_pow (by decide : 2 ≠ 0),Nat.sub_zero]
      nlinarith only [hh,hbd]

lemma trim_overlap_le_two [Fintype B] (R : A → B → Prop) {a b : A} (hab : a ≠ b) :
    (row (trim R) a ∩ row (trim R) b).card ≤ 2 := by
  apply (card_le_card (show row (trim R) a ∩ row (trim R) b ⊆
    row (clean R) a ∩ row (clean R) b from ?_)).trans (clean_overlap_le_two R hab)
  intro x hx
  exact mem_inter.mpr ⟨(mem_row _ _ _).mpr ((mem_row _ _ _).mp (mem_inter.mp hx).1).1,
    (mem_row _ _ _).mpr ((mem_row _ _ _).mp (mem_inter.mp hx).2).1⟩

/-- Triple-overlap pruning loses at most 4t incidences and leaves at most
17t light ordered pairs, including diagonals. -/
theorem trim_budget [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hmin : ∀ a, 4 ≤ (row R a).card) :
    (∑ a : A, (row R a).card) ≤ (∑ a : A, (row (trim R) a).card)+4*lightCount R ∧
      lightCount (trim R) ≤ 17*lightCount R := by
  have he := sum_le_sum (s := (univ : Finset A)) (fun a _ =>
    (trim_row_budget hf a (hmin a)).1)
  simp only [sum_add_distrib,← mul_sum] at he
  have hp := sum_le_sum (s := (univ : Finset A)) (fun a _ =>
    (trim_row_budget hf a (hmin a)).2)
  rw [← mul_sum] at hp
  have hl := inside_light_sum R univ
  have hnew := light_le_of_pair_loss R (trim R)
  omega

/-- The positive-degree rows retain at least half of their old degree.
Restricting to them changes neither incidences nor light pairs. -/
theorem normalize_rigid [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r : ℕ) (hr : 2 ≤ r) (hmin : ∀ a, 2*r ≤ (row R a).card) :
    ∃ (C : Type u) (_ : Fintype C) (f : C → A) (Q : C → B → Prop),
      Function.Injective f ∧ Fintype.card C ≤ Fintype.card A ∧
      (∀ a b, Q a b → R (f a) b) ∧ ¬ HasTheta Q ∧
      (∀ a, r ≤ (row Q a).card ∧ (row R (f a)).card ≤ 2*(row Q a).card) ∧
      (∀ a b, a ≠ b → (row Q a ∩ row Q b).card ≤ 2) ∧
      (∑ a : A, (row R a).card) ≤ (∑ a : C, (row Q a).card)+4*lightCount R ∧
      lightCount Q ≤ 17*lightCount R := by
  let S := (univ : Finset A).filter (fun a => 0 < (row (trim R) a).card)
  let Q := restrict (trim R) S
  have hzero (a : A) (ha : a ∈ univ \ S) : (row (trim R) a).card = 0 := by
    have hh := (mem_sdiff.mp ha).2
    simpa [S] using hh
  have hrow (a : S) : (row R a.val).card ≤ 2*(row Q a).card := by
    rcases trim_degree_alternative R a.val with h | h
    · have hh := (mem_filter.mp a.property).2
      omega
    · exact h
  have hE : (∑ a : S, (row Q a).card) = ∑ a : A, (row (trim R) a).card := by
    rw [restrict_incidence_sum]
    have hz : (∑ a ∈ univ \ S, (row (trim R) a).card) = 0 :=
      sum_eq_zero (fun a ha => hzero a ha)
    have hh := sum_add_sum_compl (s := S) (f := fun a => (row (trim R) a).card)
    change (∑ a ∈ S, (row (trim R) a).card) + (∑ a ∈ univ \ S, (row (trim R) a).card) =
      (∑ a : A, (row (trim R) a).card) at hh
    omega
  have hL : lightCount Q ≤ lightCount (trim R) := by
    have hh := light_restrict_le (trim R) S
    have hz : (∑ a ∈ univ \ S, (row (trim R) a).card^2) = 0 :=
      sum_eq_zero (fun a ha => by rw [hzero a ha]; rfl)
    simpa only [hz,Nat.add_zero] using hh
  have hbudget := trim_budget hf (fun a => by have := hmin a; omega)
  refine ⟨S,inferInstance,Subtype.val,Q,Subtype.val_injective,
    Fintype.card_le_of_injective _ Subtype.val_injective,?_,?_,?_,?_,?_,?_⟩
  · exact fun a b h => h.1.1
  · exact restrict_no_theta (no_theta_of_subrelation hf (trim_sub R)) S
  · intro a
    have hh := hrow a
    have hm := hmin a.val
    exact ⟨by omega,hh⟩
  · intro a b hab
    exact trim_overlap_le_two R (fun he => hab (Subtype.ext he))
  · simpa only [hE] using hbudget.1
  · exact hL.trans hbudget.2

#print axioms trim_row_budget
#print axioms trim_budget
#print axioms normalize_rigid
end Erdos713ThetaRigidNormalization
