import FormalConjecturesUtil
import Submission.ThetaRowTruncation

/-! Columns belonging to a triple overlap have many inside-row light partners.
This is an auxiliary pruning lemma, not an extremal exponent theorem. -/
open Finset
open scoped Classical
namespace Erdos713ThetaTriplePruning
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaRowTruncation
open Erdos713ThetaCrossAccounting
variable {A B : Type*}
set_option maxHeartbeats 1000000

/-- The incidence (a,x) belongs to an overlap of three distinct columns. -/
def Bad (R : A → B → Prop) (a : A) (x : B) : Prop :=
  R a x ∧ ∃ b : A, b ≠ a ∧ R b x ∧ ∃ z w : B,
    z ≠ x ∧ w ≠ x ∧ z ≠ w ∧ R a z ∧ R b z ∧ R a w ∧ R b w

noncomputable def badColumns [Fintype B] (R : A → B → Prop) (a : A) : Finset B :=
  (row R a).filter (Bad R a)

noncomputable def fan [Fintype B] (R : A → B → Prop) (a : A) (x : B) : Finset B :=
  (row R a).filter (fun y => x ≠ y ∧ codegree R x y ≤ 2)

lemma bad_fan_lower [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {a : A} {x : B} (hx : Bad R a x) :
    (row R a).card-3 ≤ (fan R a x).card := by
  obtain ⟨hax,b,hba,hbx,z,w,hzx,hwx,hzw,haz,hbz,haw,hbw⟩ := hx
  have hs : row R a \ {x,z,w} ⊆ fan R a x := by
    intro y hy
    have hy' := mem_sdiff.mp hy
    have hne : y ≠ x ∧ y ≠ z ∧ y ≠ w := by simpa using hy'.2
    refine mem_filter.mpr ⟨hy'.1,hne.1.symm,?_⟩
    exact cross_light_of_two_common hf hba hzw hzx.symm hwx.symm
      hne.2.1 hne.2.2 hne.1.symm hbz hbw haz haw hbx ((mem_row R a y).mp hy'.1)
  have hc : ({x,z,w} : Finset B).card = 3 := by simp [hzx.symm,hwx.symm,hzw]
  calc
    _ = (row R a).card-({x,z,w} : Finset B).card := by rw [hc]
    _ ≤ (row R a \ {x,z,w}).card := le_card_sdiff _ _
    _ ≤ _ := card_le_card hs

lemma bad_fan_sum [Fintype A] [Fintype B] (R : A → B → Prop) (a : A) :
    (∑ x ∈ badColumns R a, (fan R a x).card) ≤ (insideLight R a).card := by
  let Inc : B → B × B → Prop := fun x p => p.1 = x
  have habove (x : B) (hx : x ∈ badColumns R a) :
      (insideLight R a).bipartiteAbove Inc x = ({x} : Finset B) ×ˢ fan R a x := by
    have hax : R a x := (mem_row R a x).mp (mem_filter.mp hx).1
    ext p
    simp only [bipartiteAbove,insideLight,fan,mem_filter,mem_offDiag,mem_row,
      mem_product,mem_singleton,Inc]
    constructor
    · rintro ⟨⟨⟨hp1,hp2,hne⟩,hl⟩,he⟩
      subst x
      exact ⟨rfl,hp2,hne,hl⟩
    · rintro ⟨he,hp2,hne,hl⟩
      subst x
      exact ⟨⟨⟨hax,hp2,hne⟩,hl⟩,rfl⟩
  have hbelow (p : B × B) : ((badColumns R a).bipartiteBelow Inc p).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    exact (mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2
  calc
    _ = ∑ x ∈ badColumns R a, ((insideLight R a).bipartiteAbove Inc x).card := by
      apply sum_congr rfl
      intro x hx
      rw [habove x hx,card_product,card_singleton,one_mul]
    _ = ∑ p ∈ insideLight R a, ((badColumns R a).bipartiteBelow Inc p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _p ∈ insideLight R a, 1 := sum_le_sum (fun p _ => hbelow p)
    _ = _ := by simp

/-- This estimate charges inside pairs, whose global multiplicity is at most two. -/
theorem bad_columns_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (a : A) :
    (badColumns R a).card*((row R a).card-3) ≤ (insideLight R a).card := by
  calc
    _ = ∑ _x ∈ badColumns R a, ((row R a).card-3) := by simp
    _ ≤ ∑ x ∈ badColumns R a, (fan R a x).card := sum_le_sum (fun x hx =>
      bad_fan_lower hf (mem_filter.mp hx).2)
    _ ≤ _ := bad_fan_sum R a

def clean (R : A → B → Prop) (a : A) (x : B) : Prop := R a x ∧ ¬ Bad R a x

lemma clean_row [Fintype B] (R : A → B → Prop) (a : A) :
    row (clean R) a = row R a \ badColumns R a := by
  ext x
  simp only [mem_row,clean,mem_sdiff,badColumns,mem_filter]
  tauto

/-- After removing bad incidences, two different rows share at most two columns. -/
theorem clean_overlap_le_two [Fintype B] (R : A → B → Prop) {a b : A} (hab : a ≠ b) :
    (row (clean R) a ∩ row (clean R) b).card ≤ 2 := by
  by_contra h
  obtain ⟨x,z,w,hx,hz,hw,hxz,hxw,hzw⟩ := two_lt_card_iff.mp (by omega :
    2 < (row (clean R) a ∩ row (clean R) b).card)
  have hax := (mem_row (clean R) a x).mp (mem_inter.mp hx).1
  have hbx := (mem_row (clean R) b x).mp (mem_inter.mp hx).2
  have haz := (mem_row (clean R) a z).mp (mem_inter.mp hz).1
  have hbz := (mem_row (clean R) b z).mp (mem_inter.mp hz).2
  have haw := (mem_row (clean R) a w).mp (mem_inter.mp hw).1
  have hbw := (mem_row (clean R) b w).mp (mem_inter.mp hw).2
  exact hax.2 ⟨hax.1,b,hab.symm,hbx.1,z,w,hxz.symm,hxw.symm,hzw,
    haz.1,hbz.1,haw.1,hbw.1⟩

#print axioms bad_columns_bound
#print axioms clean_overlap_le_two
end Erdos713ThetaTriplePruning
