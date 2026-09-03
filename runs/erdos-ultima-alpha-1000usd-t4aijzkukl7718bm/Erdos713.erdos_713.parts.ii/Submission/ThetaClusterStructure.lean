import FormalConjecturesUtil
import Submission.ThetaHeavyShadow

/-! Structural bounds conditional on a partition of the light-pair graph.
No assertion that arbitrary theta-free relations have this partition is made. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCluster
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
variable {A B I : Type*}
set_option maxHeartbeats 2000000

lemma third_of_codegree [Fintype A] {R : A → B → Prop} {x y : B}
    (h : 3 ≤ codegree R x y) (a b : A) :
    ∃ c : A, c ≠ a ∧ c ≠ b ∧ R c x ∧ R c y := by
  classical
  let S := (univ : Finset A).filter (fun c => R c x ∧ R c y)
  have hS : 3 ≤ S.card := by
    simpa only [S,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using h
  obtain ⟨c,hcS,hc⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a,b} : Finset A).card < S.card from Finset.card_le_two.trans_lt (by omega))
  simp only [mem_insert,mem_singleton,not_or] at hc
  exact ⟨c,hc.1,hc.2,(mem_filter.mp hcS).2⟩

open scoped Classical in
noncomputable def blocks [Fintype B] (R : A → B → Prop) (τ : B → I) (a : A) : Finset I :=
  (row R a).image τ

def CrossHeavy (R : A → B → Prop) (τ : B → I) : Prop :=
  ∀ x y, τ x ≠ τ y → 3 ≤ codegree R x y

lemma no_overlap [Fintype A] [Fintype B] {R : A → B → Prop} {τ : B → I}
    (hf : ¬ HasTheta R) (hh : CrossHeavy R τ) {a b : A} (hab : a ≠ b)
    (ha : 4 ≤ (blocks R τ a).card) (hb : 3 ≤ (row R b).card)
    {z w : B} (hzw : z ≠ w) (haz : R a z) (haw : R a w)
    (hbz : R b z) (hbw : R b w) : False := by
  classical
  obtain ⟨y,hyR,hy⟩ := exists_mem_notMem_of_card_lt_card
    (show ({z,w} : Finset B).card < (row R b).card from Finset.card_le_two.trans_lt (by omega))
  have hby := (mem_row R b y).mp hyR
  simp only [mem_insert,mem_singleton,not_or] at hy
  have hsmall : ({τ z,τ w,τ y} : Finset I).card ≤ 3 := by
    exact (card_insert_le _ _).trans (by have := (Finset.card_le_two (a := τ w) (b := τ y)); omega)
  obtain ⟨i,hiR,hi⟩ := exists_mem_notMem_of_card_lt_card
    (show ({τ z,τ w,τ y} : Finset I).card < (blocks R τ a).card from hsmall.trans_lt (by omega))
  obtain ⟨x,hxR,rfl⟩ := mem_image.mp hiR
  have hax := (mem_row R a x).mp hxR
  simp only [mem_insert,mem_singleton,not_or] at hi
  have hxz : x ≠ z := fun h => hi.1 (congrArg τ h)
  have hxw : x ≠ w := fun h => hi.2.1 (congrArg τ h)
  have hxy : x ≠ y := fun h => hi.2.2 (congrArg τ h)
  obtain ⟨c,hca,hcb,hcx,hcy⟩ := third_of_codegree (hh x y hi.2.2) a b
  let f : Fin 3 → A := ![a,b,c]
  let g : Fin 4 → B := ![z,w,x,y]
  have hfi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hgi : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  exact hf ⟨f,g,hfi,hgi,haz,hbz,haw,hbw,hax,hcx,hby,hcy⟩

lemma pair_has_low [Fintype A] [Fintype B] {R : A → B → Prop} {τ : B → I}
    (hf : ¬ HasTheta R) (hh : CrossHeavy R τ) {a : A}
    (ha : 4 ≤ (blocks R τ a).card) {z w : B} (hzw : τ z ≠ τ w)
    (haz : R a z) (haw : R a w) :
    ∃ b : A, (row R b).card ≤ 2 ∧ row R b = {z,w} := by
  classical
  have hne : z ≠ w := fun h => hzw (congrArg τ h)
  obtain ⟨b,hba,_,hbz,hbw⟩ := third_of_codegree (hh z w hzw) a a
  have hlow : (row R b).card ≤ 2 := by
    by_contra hbad
    exact no_overlap hf hh hba.symm ha (by omega) hne haz haw hbz hbw
  have hsub : ({z,w} : Finset B) ⊆ row R b := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> apply (mem_row R _ _).mpr <;> assumption
  refine ⟨b,hlow,(eq_of_subset_of_card_le hsub ?_).symm⟩
  simpa [hne] using hlow

open scoped Classical in
noncomputable def spoke (τ : B → I) (z w x : B) : Finset B :=
  if τ x = τ z then {x,w} else {x,z}

lemma spoke_data (τ : B → I) {z w x : B} (hzw : τ z ≠ τ w) :
    (spoke τ z w x).card = 2 ∧
    ∃ y, (y = z ∨ y = w) ∧ τ x ≠ τ y ∧ spoke τ z w x = {x,y} := by
  classical
  by_cases hx : τ x = τ z
  · have hne : τ x ≠ τ w := hx ▸ hzw
    exact ⟨by simp [spoke,hx,show x ≠ w from fun h => hne (congrArg τ h)],w,
      Or.inr rfl,hne,by simp [spoke,hx]⟩
  · exact ⟨by simp [spoke,hx,show x ≠ z from fun h => hx (congrArg τ h)],z,
      Or.inl rfl,hx,by simp [spoke,hx]⟩

lemma spoke_injective (τ : B → I) {z w : B} (hzw : τ z ≠ τ w) :
    Function.Injective (fun x : {x : B // x ≠ z} => spoke τ z w x.val) := by
  classical
  intro x y he
  change spoke τ z w x.val = spoke τ z w y.val at he
  apply Subtype.ext
  by_cases hx : τ x.val = τ z <;> by_cases hy : τ y.val = τ z
  · have hxe : x.val ≠ w := fun h => hzw (hx.symm.trans (congrArg τ h))
    have hye : y.val ≠ w := fun h => hzw (hy.symm.trans (congrArg τ h))
    simp only [spoke,hx,hy,if_true] at he
    have hh := congrArg (fun P : Finset B => x.val ∈ P) he
    simpa [hxe] using hh.mp (by simp)
  · have hz : z ∈ spoke τ z w y.val := by simp [spoke,hy]
    rw [← he] at hz
    have hne : z ≠ w := fun h => hzw (congrArg τ h)
    simp [spoke,hx,hne,Ne.symm x.property] at hz
  · have hz : z ∈ spoke τ z w x.val := by simp [spoke,hx]
    rw [he] at hz
    have hne : z ≠ w := fun h => hzw (congrArg τ h)
    simp [spoke,hy,hne,Ne.symm y.property] at hz
  · simp only [spoke,hx,hy,if_false] at he
    have hh := congrArg (fun P : Finset B => x.val ∈ P) he
    simpa [x.property] using hh.mp (by simp)

#print axioms no_overlap
#print axioms pair_has_low
#print axioms spoke_injective
end Erdos713ThetaCluster
