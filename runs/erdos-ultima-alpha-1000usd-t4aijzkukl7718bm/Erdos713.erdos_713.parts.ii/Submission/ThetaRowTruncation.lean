import FormalConjecturesUtil
import Submission.ThetaAllWitnessPacking

/-! An unweighted outside-column packing bound and a large-row truncation
for oriented-theta-free relations. These are auxiliary finite statements;
they do not establish the rationality conjecture. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRowTruncation
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
open Erdos713ThetaPrivatePetals Erdos713ThetaAllWitnessPacking
variable {A B : Type*}
set_option maxHeartbeats 2000000

/-- Summing just the outside petals, rather than the whole zero-pair
rectangles, costs six per column at a fixed root. -/
theorem private_sum_le [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (a : A) (ha : a ∈ S) :
    (∑ w : ↥(witnesses R S a),
      (privatePetal R S w.val.1 w.val.2).card) ≤ 6*Fintype.card B := by
  let P := ↥(witnesses R S a)
  let Inc : P → B → Prop := fun w y => y ∈ privatePetal R S w.val.1 w.val.2
  have habove (w : P) : (univ : Finset B).bipartiteAbove Inc w =
      privatePetal R S w.val.1 w.val.2 := by
    ext y
    simp [bipartiteAbove,Inc]
  have hbelow (y : B) : ((univ : Finset P).bipartiteBelow Inc y).card ≤ 6 := by
    by_cases hay : R a y
    · have he : (univ : Finset P).bipartiteBelow Inc y = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hy := (mem_privatePetal R S w.val.1 w.val.2 y).mp
          (mem_filter.mp hw).2
        have h := (mem_witnesses R S a w.val).mp w.property
        have hp := mem_offDiag.mp (mem_filter.mp h.1).1
        have ham : a ∈ commonRows R S w.val.1 := mem_filter.mpr
          ⟨ha,(mem_row R _ _).mp hp.1,(mem_row R _ _).mp hp.2.1⟩
        exact hy.2.2.2 a ham h.2.2.symm hay
      simp [he]
    · exact private_multiplicity hf S a y hay
  calc
    _ = ∑ w : P, ((univ : Finset B).bipartiteAbove Inc w).card := by
      simp only [habove,P]
    _ = ∑ y : B, ((univ : Finset P).bipartiteBelow Inc y).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _y : B, 6 := sum_le_sum (fun y _ => hbelow y)
    _ = _ := by simp [Nat.mul_comm]

/-- Unlike the zero-pair rectangle bound, this bound contains no column
degree factor and no light-pair count. -/
theorem witness_external_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card) (a : A) (ha : a ∈ S) :
    (witnesses R S a).card*(r-3) ≤ 6*Fintype.card B := by
  have hp (w : ↥(witnesses R S a)) :
      r-3 ≤ (privatePetal R S w.val.1 w.val.2).card := by
    have h := (mem_witnesses R S a w.val).mp w.property
    have hpair := mem_offDiag.mp (mem_filter.mp h.1).1
    have hb := mem_filter.mp h.2.1
    exact (Nat.sub_le_sub_right (hmin _ hb.1) 3).trans
      (privatePetal_card_lower hf S hpair.2.2 (anchor_heavy h.1) hb.2)
  calc
    _ = ∑ _w : ↥(witnesses R S a), (r-3) := by simp
    _ ≤ ∑ w : ↥(witnesses R S a),
        (privatePetal R S w.val.1 w.val.2).card := sum_le_sum (fun w _ => hp w)
    _ ≤ _ := private_sum_le hf S a ha

lemma twice_anchors_le_witnesses [Fintype B] (R : A → B → Prop)
    (S : Finset A) (a : A) (ha : a ∈ S) :
    2*(anchors R S a).card ≤ (witnesses R S a).card := by
  rw [witnesses_card R S a ha]
  calc
    _ = ∑ _p ∈ anchors R S a, 2 := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum (fun p hp => by
      have hh := (mem_filter.mp hp).2
      omega)

theorem anchor_external_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card) (a : A) (ha : a ∈ S) :
    (anchors R S a).card*(r-3) ≤ 3*Fintype.card B := by
  have h := witness_external_bound hf S r hmin a ha
  have hh := Nat.mul_le_mul_right (r-3) (twice_anchors_le_witnesses R S a ha)
  nlinarith only [h,hh]

noncomputable def insideLight [Fintype B] (R : A → B → Prop) (a : A) : Finset (B × B) :=
  (row R a).offDiag.filter (fun p => codegree R p.1 p.2 ≤ 2)

lemma row_pair_split [Fintype A] [Fintype B] (R : A → B → Prop) (a : A) :
    (row R a).offDiag.card =
      (anchors R univ a).card + (insideLight R a).card := by
  have hc (p : B × B) : (commonRows R univ p).card = codegree R p.1 p.2 := by
    simp [commonRows,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : (insideLight R a) = (row R a).offDiag.filter
      (fun p => ¬ 3 ≤ (commonRows R univ p).card) := by
    ext p
    simp only [insideLight,mem_filter,hc,not_le,Nat.lt_succ_iff]
  rw [he,anchors]
  exact (card_filter_add_card_filter_not _).symm

/-- Inside-row light pairs have multiplicity at most two globally. -/
theorem inside_light_sum [Fintype A] [Fintype B] (R : A → B → Prop) (S : Finset A) :
    (∑ a ∈ S, (insideLight R a).card) ≤ 2*lightCount R := by
  let Inc : A → B × B → Prop := fun a p =>
    R a p.1 ∧ R a p.2 ∧ p.1 ≠ p.2
  have habove (a : A) : (lightSet R).bipartiteAbove Inc a = insideLight R a := by
    ext p
    simp only [bipartiteAbove,insideLight,lightSet,mem_filter,mem_univ,true_and,
      mem_offDiag,mem_row,Inc]
    tauto
  have hbelow (p : B × B) (hp : p ∈ lightSet R) :
      (S.bipartiteBelow Inc p).card ≤ 2 := by
    have hsub : S.bipartiteBelow Inc p ⊆
        (univ : Finset A).filter (fun a => R a p.1 ∧ R a p.2) := by
      intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2.1,
        (mem_filter.mp ha).2.2.1⟩
    have hh := (mem_filter.mp hp).2
    have hc : ((univ : Finset A).filter (fun a => R a p.1 ∧ R a p.2)).card ≤ 2 := by
      simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
    exact (card_le_card hsub).trans hc
  calc
    _ = ∑ a ∈ S, ((lightSet R).bipartiteAbove Inc a).card := by simp only [habove]
    _ = ∑ p ∈ lightSet R, (S.bipartiteBelow Inc p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _p ∈ lightSet R, 2 := sum_le_sum (fun p hp => hbelow p hp)
    _ = _ := by simp [lightSet_card,Nat.mul_comm]

/-- After a minimum-row-degree-four restriction, rows above the square-root
column scale are paid for by inside light pairs, with no degree weight. -/
theorem large_row_squares [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hmin : ∀ a, 4 ≤ (row R a).card) (S : Finset A)
    (hS : ∀ a ∈ S, 12*Fintype.card B ≤ (row R a).card^2) :
    (∑ a ∈ S, (row R a).card^2) ≤ 4*lightCount R := by
  have hp (a : A) (ha : a ∈ S) :
      (row R a).card^2 ≤ 2*(insideLight R a).card := by
    have h := anchor_external_bound hf univ 4 (fun b _ => hmin b) a (mem_univ _)
    norm_num only at h
    have he := row_pair_split R a
    rw [offDiag_card] at he
    have hr := hmin a
    have hle := hS a ha
    have hs : (row R a).card*(row R a).card-(row R a).card + (row R a).card =
        (row R a).card*(row R a).card := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hsum := sum_le_sum (s := S) (fun a ha => hp a ha)
  rw [← mul_sum] at hsum
  have hl := inside_light_sum R S
  omega

/-- In particular the incidence loss in such a truncation is at most the
original light-pair count: every removed row has degree at least four. -/
theorem large_row_incidences [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hmin : ∀ a, 4 ≤ (row R a).card) (S : Finset A)
    (hS : ∀ a ∈ S, 12*Fintype.card B ≤ (row R a).card^2) :
    (∑ a ∈ S, (row R a).card) ≤ lightCount R := by
  have hl := large_row_squares hf hmin S hS
  have hp (a : A) : 4*(row R a).card ≤ (row R a).card^2 := by
    have hh := hmin a
    nlinarith
  have hs := sum_le_sum (s := S) (fun a _ => hp a)
  rw [← mul_sum] at hs
  omega


/-- A higher minimum row degree lowers the truncation scale. -/
theorem large_row_squares_at [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r : ℕ) (hr : 4 ≤ r)
    (hmin : ∀ a, r ≤ (row R a).card) (S : Finset A)
    (hS : ∀ a ∈ S, 12*Fintype.card B ≤ (row R a).card^2*(r-3)) :
    (∑ a ∈ S, (row R a).card^2) ≤ 4*lightCount R := by
  have hp (a : A) (ha : a ∈ S) :
      (row R a).card^2 ≤ 2*(insideLight R a).card := by
    have h := anchor_external_bound hf univ r (fun b _ => hmin b) a (mem_univ _)
    have he := row_pair_split R a
    rw [offDiag_card] at he
    have hd : 4 ≤ (row R a).card := hr.trans (hmin a)
    have hle := hS a ha
    have hs : (row R a).card*(row R a).card-(row R a).card + (row R a).card =
        (row R a).card*(row R a).card := Nat.sub_add_cancel (by nlinarith)
    have he' : (row R a).card^2 =
        (anchors R univ a).card + (insideLight R a).card + (row R a).card := by
      nlinarith only [he,hs]
    have hmul := congrArg (fun n : ℕ => n*(r-3)) he'
    have hd' : 4*(row R a).card ≤ (row R a).card^2 := by nlinarith
    have hdmul := Nat.mul_le_mul_right (r-3) hd'
    have htarget : (row R a).card^2*(r-3) ≤ 2*(insideLight R a).card*(r-3) := by
      nlinarith only [h,hle,hmul,hdmul]
    exact Nat.le_of_mul_le_mul_right htarget (by omega : 0 < r-3)
  have hsum := sum_le_sum (s := S) (fun a ha => hp a ha)
  rw [← mul_sum] at hsum
  have hl := inside_light_sum R S
  omega

theorem large_row_incidences_at [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r : ℕ) (hr : 4 ≤ r)
    (hmin : ∀ a, r ≤ (row R a).card) (S : Finset A)
    (hS : ∀ a ∈ S, 12*Fintype.card B ≤ (row R a).card^2*(r-3)) :
    (∑ a ∈ S, (row R a).card) ≤ lightCount R := by
  have hl := large_row_squares_at hf r hr hmin S hS
  have hp (a : A) : 4*(row R a).card ≤ (row R a).card^2 := by
    have hh : 4 ≤ (row R a).card := hr.trans (hmin a)
    nlinarith
  have hs := sum_le_sum (s := S) (fun a _ => hp a)
  rw [← mul_sum] at hs
  omega

#print axioms large_row_squares_at
#print axioms large_row_incidences_at

#print axioms private_sum_le
#print axioms witness_external_bound
#print axioms anchor_external_bound
#print axioms inside_light_sum
#print axioms large_row_squares
#print axioms large_row_incidences
end Erdos713ThetaRowTruncation
