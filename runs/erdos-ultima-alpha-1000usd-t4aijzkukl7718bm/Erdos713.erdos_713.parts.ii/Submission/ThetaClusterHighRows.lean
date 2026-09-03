import FormalConjecturesUtil
import Submission.ThetaClusterStructure

/-! Rows meeting four partition classes have only linear total incidence,
provided all cross-class column pairs are heavy. -/
open Finset
open scoped Classical
namespace Erdos713ThetaCluster
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
variable {A B I : Type*}
set_option maxHeartbeats 2000000

lemma high_unique [Fintype A] [Fintype B] {R : A → B → Prop} {τ : B → I}
    (hf : ¬ HasTheta R) (hh : CrossHeavy R τ) {a b : A}
    (ha : 4 ≤ (blocks R τ a).card) (hb : 4 ≤ (blocks R τ b).card)
    (P : Finset B) (hP : P.card = 2) (hPa : P ⊆ row R a) (hPb : P ⊆ row R b) : a = b := by
  obtain ⟨z,w,hzw,rfl⟩ := card_eq_two.mp hP
  by_contra hab
  have hb' : 3 ≤ (row R b).card := by
    have hi : (blocks R τ b).card ≤ (row R b).card := card_image_le
    omega
  exact no_overlap hf hh hab ha hb' hzw
    ((mem_row R a z).mp (hPa (by simp))) ((mem_row R a w).mp (hPa (by simp)))
    ((mem_row R b z).mp (hPb (by simp))) ((mem_row R b w).mp (hPb (by simp)))

noncomputable def manyBlocks [Fintype A] [Fintype B] (R : A → B → Prop) (τ : B → I) : Finset A :=
  univ.filter (fun a => 4 ≤ (blocks R τ a).card)

lemma high_incidence_le [Fintype A] [Fintype B] {R : A → B → Prop} {τ : B → I}
    (hf : ¬ HasTheta R) (hh : CrossHeavy R τ) :
    (∑ a ∈ manyBlocks R τ, (row R a).card) ≤ 2*Fintype.card A := by
  let H := ↥(manyBlocks R τ)
  have hhigh (a : H) : 4 ≤ (blocks R τ a.val).card := (mem_filter.mp a.property).2
  have hanchors (a : H) : ∃ z ∈ row R a.val, ∃ w ∈ row R a.val, τ z ≠ τ w := by
    obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp (show 1 < (blocks R τ a.val).card by have := hhigh a; omega)
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hi
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
    exact ⟨z,hz,w,hw,hij⟩
  choose z hz w hw hzw using hanchors
  have hsub (a : H) (x : B) (hx : x ∈ row R a.val) :
      spoke τ (z a) (w a) x ⊆ row R a.val := by
    obtain ⟨_,y,hy,_,he⟩ := spoke_data τ (hzw a) (x := x)
    rw [he]
    rcases hy with rfl | rfl
    · simpa [insert_subset_iff] using And.intro hx (hz a)
    · simpa [insert_subset_iff] using And.intro hx (hw a)
  let T := (a : H) × ((row R a.val).erase (z a))
  have hex (p : T) : ∃ b : A, row R b = spoke τ (z p.1) (w p.1) p.2.val := by
    obtain ⟨_,y,hy,hxy,he⟩ := spoke_data τ (hzw p.1) (x := p.2.val)
    have hx := (mem_erase.mp p.2.property).2
    have hyR : R p.1.val y := by
      rcases hy with rfl | rfl
      · exact (mem_row _ _ _).mp (hz p.1)
      · exact (mem_row _ _ _).mp (hw p.1)
    obtain ⟨b,_,hb⟩ := pair_has_low hf hh (hhigh p.1) hxy ((mem_row _ _ _).mp hx) hyR
    exact ⟨b,hb.trans he.symm⟩
  choose b hb using hex
  have hinj : Function.Injective b := by
    rintro ⟨a,x⟩ ⟨a',y⟩ he
    have hP : spoke τ (z a) (w a) x.val = spoke τ (z a') (w a') y.val :=
      (hb ⟨a,x⟩).symm.trans ((congrArg (fun b => row R b) he).trans (hb ⟨a',y⟩))
    have haa : a = a' := by
      apply Subtype.ext
      apply high_unique hf hh (hhigh a) (hhigh a') (spoke τ (z a) (w a) x.val)
        (spoke_data τ (hzw a)).1 (hsub a x.val (mem_erase.mp x.property).2)
      rw [hP]
      exact hsub a' y.val (mem_erase.mp y.property).2
    subst a'
    have hxy : x.val = y.val := congrArg (fun v : {v : B // v ≠ z a} => v.val)
      (spoke_injective τ (hzw a) (a₁ := ⟨x.val,(mem_erase.mp x.property).1⟩)
        (a₂ := ⟨y.val,(mem_erase.mp y.property).1⟩) hP)
    congr 1
    exact Subtype.ext hxy
  have hc := Fintype.card_le_of_injective b hinj
  have he (a : H) : (row R a.val).card = ((row R a.val).erase (z a)).card+1 := by
    rw [card_erase_of_mem (hz a)]
    have hp : 0 < (row R a.val).card := card_pos.mpr ⟨z a,hz a⟩
    omega
  have hH : Fintype.card H ≤ Fintype.card A := by
    exact Fintype.card_le_of_injective (fun a : H => a.val) Subtype.val_injective
  have hc' : (∑ a : H, ((row R a.val).erase (z a)).card) ≤ Fintype.card A := by
    simpa only [T,Fintype.card_sigma,Fintype.card_coe] using hc
  calc
    _ = ∑ a : H, (row R a.val).card := (sum_coe_sort _ _).symm
    _ = (∑ a : H, ((row R a.val).erase (z a)).card)+Fintype.card H := by
      simp only [he,sum_add_distrib,sum_const,card_univ,Nat.nsmul_eq_mul,mul_one]
    _ ≤ 2*Fintype.card A := by omega

#print axioms high_incidence_le
end Erdos713ThetaCluster
