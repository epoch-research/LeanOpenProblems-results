import FormalConjecturesUtil
import Submission.ThetaAnchorPacking

/-! Private neighbours in a book of rows through a heavy column pair. -/
open Finset
namespace Erdos713ThetaPrivatePetals
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma theta_of_rows {R : A → B → Prop} {a b c : A} {z w x y : B}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hzw : z ≠ w) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hxy : x ≠ y)
    (haz : R a z) (haw : R a w) (hbz : R b z) (hbw : R b w)
    (hax : R a x) (hby : R b y) (hcx : R c x) (hcy : R c y) : HasTheta R := by
  classical
  let f : Fin 3 → A := ![a,b,c]
  let g : Fin 4 → B := ![z,w,x,y]
  have hfi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hgi : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  exact ⟨f,g,hfi,hgi,haz,hbz,haw,hbw,hax,hcx,hby,hcy⟩

open scoped Classical in
lemma intersection_le_three [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {a b : A} (hab : a ≠ b) {p : B × B}
    (hp : p.1 ≠ p.2) (hheavy : 3 ≤ codegree R p.1 p.2)
    (ha : R a p.1 ∧ R a p.2) (hb : R b p.1 ∧ R b p.2) :
    (row R a ∩ row R b).card ≤ 3 := by
  by_contra h
  have hh := large_overlap_cross_light hf hab (by omega) hp ha.1 hb.2
  omega

open scoped Classical in
noncomputable def sharedPetal [Fintype B] (R : A → B → Prop)
    (S : Finset A) (p : B × B) (b : A) : Finset B :=
  (row R b \ {p.1,p.2}).filter (fun y =>
    ∃ c ∈ commonRows R S p, c ≠ b ∧ R c y)

open scoped Classical in
noncomputable def privatePetal [Fintype B] (R : A → B → Prop)
    (S : Finset A) (p : B × B) (b : A) : Finset B :=
  (row R b \ {p.1,p.2}) \ sharedPetal R S p b

open scoped Classical in
/-- A row in a heavy-pair book has at most one non-anchor column shared
with other rows of that book. -/
theorem sharedPetal_card_le_one [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) {p : B × B} {b : A}
    (hp : p.1 ≠ p.2) (hheavy : 3 ≤ codegree R p.1 p.2)
    (hb : R b p.1 ∧ R b p.2) : (sharedPetal R S p b).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxout,c,hcp,hcb,hcx⟩ := mem_filter.mp hx
  obtain ⟨hyout,d,hdp,hdb,hdy⟩ := mem_filter.mp hy
  have hbx := (mem_row R b x).mp (mem_sdiff.mp hxout).1
  have hby := (mem_row R b y).mp (mem_sdiff.mp hyout).1
  have hxne : x ≠ p.1 ∧ x ≠ p.2 := by simpa using (mem_sdiff.mp hxout).2
  have hyne : y ≠ p.1 ∧ y ≠ p.2 := by simpa using (mem_sdiff.mp hyout).2
  have hc := (mem_filter.mp hcp).2
  have hd := (mem_filter.mp hdp).2
  by_contra hxy
  by_cases hcd : c = d
  · subst d
    have hcard := intersection_le_three hf hcb.symm hp hheavy hb hc
    have hsub : ({p.1,p.2,x,y} : Finset B) ⊆ row R b ∩ row R c := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> simp [mem_row,hb,hc,hbx,hcx,hby,hdy]
    have hfour : ({p.1,p.2,x,y} : Finset B).card = 4 := by
      simp [hp,hxy,Ne.symm hxne.1,Ne.symm hxne.2,
        Ne.symm hyne.1,Ne.symm hyne.2]
    have hh := card_le_card hsub
    omega
  · exact hf (theta_of_rows hcd hcb.symm hdb.symm hp hxne.1 hxne.2
      hyne.1 hyne.2 hxy hc.1 hc.2 hd.1 hd.2 hcx hdy hbx hby)

open scoped Classical in
lemma mem_privatePetal [Fintype B] (R : A → B → Prop) (S : Finset A)
    (p : B × B) (b : A) (y : B) :
    y ∈ privatePetal R S p b ↔
      R b y ∧ y ≠ p.1 ∧ y ≠ p.2 ∧
        ∀ c ∈ commonRows R S p, c ≠ b → ¬ R c y := by
  classical
  simp only [privatePetal,sharedPetal,mem_sdiff,mem_filter,mem_insert,mem_singleton,
    mem_row,not_or,not_and,not_exists]
  tauto

open scoped Classical in
/-- At least degree(b)-3 columns are private to b within the retained book. -/
theorem privatePetal_card_lower [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) {p : B × B} {b : A}
    (hp : p.1 ≠ p.2) (hheavy : 3 ≤ codegree R p.1 p.2)
    (hb : R b p.1 ∧ R b p.2) :
    (row R b).card-3 ≤ (privatePetal R S p b).card := by
  classical
  have hs := sharedPetal_card_le_one hf S hp hheavy hb
  have hsub : ({p.1,p.2} : Finset B) ⊆ row R b := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [mem_row,hb]
  have ho : (row R b \ {p.1,p.2}).card = (row R b).card-2 := by
    rw [card_sdiff_of_subset hsub]
    simp [hp]
  have hi : (sharedPetal R S p b ∩ (row R b \ {p.1,p.2})).card ≤ 1 :=
    (card_le_card inter_subset_left).trans hs
  rw [privatePetal,card_sdiff,ho]
  omega

#print axioms intersection_le_three
#print axioms sharedPetal_card_le_one
#print axioms privatePetal_card_lower
end Erdos713ThetaPrivatePetals
