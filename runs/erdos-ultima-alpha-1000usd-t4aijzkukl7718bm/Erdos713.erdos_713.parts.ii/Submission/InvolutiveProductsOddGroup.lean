import FormalConjecturesUtil
import Submission.DenseLowProductValues

/-! An involution on at least forty parameters forces a nondegenerate
product relation in an odd abelian group of order at most one larger. -/
open Finset
open scoped Pointwise
namespace Erdos713InvolutiveProductsOddGroup
variable {I W : Type*} [Fintype I] [CommGroup W] [DecidableEq I] [DecidableEq W]
set_option maxHeartbeats 2000000

def Avoid (τ : I → I) (B : I → W) : Prop :=
  ∀ c r d, c ≠ r → c ≠ τ r → c ≠ d → c ≠ τ d → B c*B (τ c) ≠ B r*B d

def pairProduct (τ : I → I) (B : I → W) (c : I) : W := B c*B (τ c)

variable (τ : I → I) (hτ : Function.Involutive τ) (B : I → W)

include hτ

omit [Fintype I] [DecidableEq I] [DecidableEq W] in
lemma pairProduct_tau (c : I) : pairProduct τ B (τ c) = pairProduct τ B c := by
  simp only [pairProduct,hτ c,mul_comm]

omit [Fintype I] [DecidableEq W] in
lemma pairProduct_fiber (h : Avoid τ B) {c r : I}
    (he : pairProduct τ B c = pairProduct τ B r) : r=c ∨ r=τ c := by
  by_cases hr : r=c
  · exact Or.inl hr
  by_cases hr' : r=τ c
  · exact Or.inr hr'
  have hc : c ≠ τ r := by
    intro hh
    exact hr' (by simpa only [hτ r] using (congrArg τ hh).symm)
  exact (h c r (τ r) (Ne.symm hr) hc hc (by simpa only [hτ r] using (Ne.symm hr)) he).elim

lemma exclusive_in_pair (h : Avoid τ B) (c : I) :
    ∃ i, (i=c ∨ i=τ c) ∧ ∀ j, B j=B i → j=c ∨ j=τ c := by
  classical
  by_cases hc : ∀ j, B j=B c → j=c ∨ j=τ c
  · exact ⟨c,Or.inl rfl,hc⟩
  push_neg at hc
  obtain ⟨r,hr,hrc,hrτ⟩ := hc
  refine ⟨τ c,Or.inr rfl,?_⟩
  intro d hd
  by_contra hn
  push_neg at hn
  have hcτ : c ≠ τ r := by
    intro hh
    exact hrτ (by simpa only [hτ r] using (congrArg τ hh).symm)
  have hcdτ : c ≠ τ d := by
    intro hh
    exact hn.2 (by simpa only [hτ d] using (congrArg τ hh).symm)
  exact h c r d hrc.symm hcτ hn.1.symm hcdτ (by rw [hr,hd])

lemma image_pairProduct_le_image (h : Avoid τ B) :
    (Finset.univ.image (pairProduct τ B)).card ≤ (Finset.univ.image B).card := by
  classical
  let D := Finset.univ.image (pairProduct τ B)
  let R := Finset.univ.image B
  have hex (p : D) : ∃ i : I, ∀ j, B j=B i → pairProduct τ B j=p.val := by
    obtain ⟨c,_,hc⟩ := mem_image.mp p.property
    obtain ⟨i,hi,hij⟩ := exclusive_in_pair τ hτ B h c
    refine ⟨i,?_⟩
    intro j he
    rcases hij j he with rfl | rfl
    · exact hc
    · exact (pairProduct_tau τ hτ B c).trans hc
  choose i hi using hex
  let f : D → R := fun p => ⟨B (i p),mem_image_of_mem B (mem_univ _)⟩
  have hf : Function.Injective f := by
    intro p q he
    have hb : B (i p)=B (i q) := congrArg Subtype.val he
    exact Subtype.ext ((hi p (i q) hb.symm).symm.trans (hi q (i q) rfl))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma twice_image_pairProduct (hfix : ∀ c, τ c ≠ c) (h : Avoid τ B) :
    2*(Finset.univ.image (pairProduct τ B)).card = Fintype.card I := by
  classical
  let D := Finset.univ.image (pairProduct τ B)
  have hfib (p : W) (hp : p ∈ D) :
      (Finset.univ.filter (fun c => pairProduct τ B c=p)).card = 2 := by
    obtain ⟨c,_,rfl⟩ := mem_image.mp hp
    have he : Finset.univ.filter (fun r => pairProduct τ B r=pairProduct τ B c) = {c,τ c} := by
      ext r
      simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      constructor
      · intro hh
        exact pairProduct_fiber τ hτ B h hh.symm
      · rintro (rfl | rfl)
        · rfl
        · exact pairProduct_tau τ hτ B c
    rw [he,card_pair (hfix c).symm]
  have he := Finset.card_eq_sum_card_image (pairProduct τ B) (Finset.univ : Finset I)
  change Fintype.card I = ∑ p ∈ D, (Finset.univ.filter (fun c => pairProduct τ B c=p)).card at he
  have hs : (∑ p ∈ D, (Finset.univ.filter (fun c => pairProduct τ B c=p)).card) = 2*D.card := by
    calc
      _ = ∑ _p ∈ D, 2 := sum_congr rfl hfib
      _ = _ := by simp [Nat.mul_comm]
  exact (he.trans hs).symm

omit [Fintype I] [DecidableEq W] in
lemma first_value (h : Avoid τ B) (c r d : I)
    (he : pairProduct τ B c = B r*B d) : B r=B c ∨ B r=B (τ c) := by
  by_cases hcr : c=r
  · exact Or.inl (congrArg B hcr.symm)
  by_cases hcr' : c=τ r
  · right
    exact congrArg B (by simpa only [hτ r] using (congrArg τ hcr').symm)
  by_cases hcd : c=d
  · right
    subst d
    apply mul_right_cancel (b := B c)
    exact he.symm.trans (mul_comm _ _)
  by_cases hcd' : c=τ d
  · left
    have hd : d=τ c := by simpa only [hτ d] using (congrArg τ hcd').symm
    rw [hd] at he
    exact (mul_right_cancel he).symm
  exact (h c r d hcr hcr' hcd hcd' he).elim

lemma low_products (h : Avoid τ B) (p : W) (hp : p ∈ Finset.univ.image (pairProduct τ B)) :
    ((Finset.univ.image B) ∩ p • (Finset.univ.image B)⁻¹).card ≤ 2 := by
  obtain ⟨c,_,rfl⟩ := mem_image.mp hp
  apply (card_le_card (show (Finset.univ.image B) ∩ pairProduct τ B c • (Finset.univ.image B)⁻¹ ⊆
      {B c,B (τ c)} from ?_)).trans card_le_two
  intro x hx
  obtain ⟨r,_,rfl⟩ := mem_image.mp (mem_inter.mp hx).1
  obtain ⟨z,hz,hzB⟩ := mem_smul_finset.mp (mem_inter.mp hx).2
  obtain ⟨y,hy,rfl⟩ := mem_inv.mp hz
  obtain ⟨d,_,rfl⟩ := mem_image.mp hy
  change pairProduct τ B c*(B d)⁻¹=B r at hzB
  have he : pairProduct τ B c=B r*B d := by
    calc
      _ = (pairProduct τ B c*(B d)⁻¹)*B d := by simp [mul_assoc]
      _ = _ := by rw [hzB]
  simpa only [mem_insert,mem_singleton] using first_value τ hτ B h c r d he

/-- No regularity, injectivity, polynomial form, or fiber bound on B is
needed. The odd-order and near-equal-cardinality assumptions are explicit. -/
theorem exists_relation [Fintype W] (hfix : ∀ c, τ c ≠ c)
    (hodd : Odd (Fintype.card W)) (hW : Fintype.card W ≤ Fintype.card I+1)
    (hI : 40 ≤ Fintype.card I) :
    ∃ c r d, c ≠ r ∧ c ≠ τ r ∧ c ≠ d ∧ c ≠ τ d ∧
      B c*B (τ c)=B r*B d := by
  classical
  by_contra hno
  have h : Avoid τ B := by
    intro c r d hcr hcr' hcd hcd' he
    exact hno ⟨c,r,d,hcr,hcr',hcd,hcd',he⟩
  have hD := twice_image_pairProduct τ hτ B hfix h
  apply Erdos713DenseLowProductValues.impossible (Finset.univ.image B)
    (Finset.univ.image (pairProduct τ B)) hodd (by omega)
    (image_pairProduct_le_image τ hτ B h) (by omega)
    (low_products τ hτ B h)

#print axioms image_pairProduct_le_image
#print axioms twice_image_pairProduct
#print axioms exists_relation
end Erdos713InvolutiveProductsOddGroup
