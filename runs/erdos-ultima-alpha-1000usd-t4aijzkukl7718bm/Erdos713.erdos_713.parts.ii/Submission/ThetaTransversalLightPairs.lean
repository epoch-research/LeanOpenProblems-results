import FormalConjecturesUtil
import Submission.ThetaTransversalCompletion

/-! Cross-copy pairs have codegree one, not three. Consequently the
transversal construction does not refute the light-pair-weighted bound. -/
open Finset
namespace Erdos713ThetaTransversalLight
open Erdos713ThetaTransversal Erdos713GlobalLight Erdos713ThetaSplit
open Erdos713ThetaCross (lightCount)
variable {A I F : Type*} [Field F]
set_option maxHeartbeats 2000000

lemma cross_codegree_one [Fintype A] [Fintype I] [Fintype F]
    (s : I → F) (hs : Function.Injective s) (R : A → F → Prop)
    (x y : I × F) (hi : x.1 ≠ y.1) : codegree (complete s R) x y = 1 := by
  classical
  let U := {a : Rows I A F // complete s R a x ∧ complete s R a y}
  haveI : Nonempty U := (Nat.card_pos_iff.mp (cross_positive s hs R x y hi)).1
  haveI : Subsingleton U := ⟨by
    intro a b
    apply Subtype.ext
    by_contra hab
    obtain ⟨⟨p,hp⟩,_⟩ := branches_old s hs R hab (fun he => hi (congrArg Prod.fst he))
      a.property.1 a.property.2 b.property.1 b.property.2
    have hpx := a.property.1
    have hpy := a.property.2
    rw [hp] at hpx hpy
    exact hi (hpx.1.symm.trans hpy.1)⟩
  exact Nat.card_unique

lemma light_count_lower [Fintype A] [Fintype I] [Fintype F]
    (s : I → F) (hs : Function.Injective s) (R : A → F → Prop) :
    (Nat.card I)*(Nat.card I-1)*(Nat.card F)^2 ≤ lightCount (complete s R) := by
  classical
  let U := ↥((univ : Finset I).offDiag) × (F × F)
  let V := {p : (I × F) × (I × F) // codegree (complete s R) p.1 p.2 ≤ 2}
  let f : U → V := fun p => ⟨((p.1.val.1,p.2.1),(p.1.val.2,p.2.2)),by
    have hi := (mem_offDiag.mp p.1.property).2.2
    rw [cross_codegree_one s hs R _ _ hi]
    decide⟩
  have hf : Function.Injective f := by
    intro p q he
    have hi := congrArg (fun z : V => z.val.1.1) he
    have hj := congrArg (fun z : V => z.val.2.1) he
    have hx := congrArg (fun z : V => z.val.1.2) he
    have hy := congrArg (fun z : V => z.val.2.2) he
    exact Prod.ext (Subtype.ext (Prod.ext hi hj)) (Prod.ext hx hy)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [U,V,lightCount,Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_prod,
    offDiag_card,card_univ,pow_two,Nat.mul_sub_left_distrib,Nat.mul_one] using hh

lemma column_square_le_light [Fintype A] [Fintype I] [Fintype F]
    (s : I → F) (hs : Function.Injective s) (R : A → F → Prop) (hI : 2 ≤ Nat.card I) :
    (Nat.card (I × F))^2 ≤ 2*lightCount (complete s R) := by
  have ht : (Nat.card I)^2 ≤ 2*(Nat.card I*(Nat.card I-1)) := by
    have hsub : Nat.card I-1+1 = Nat.card I := Nat.sub_add_cancel (by omega)
    nlinarith
  calc
    _ = (Nat.card I)^2*(Nat.card F)^2 := by rw [Nat.card_prod,mul_pow]
    _ ≤ (2*(Nat.card I*(Nat.card I-1)))*(Nat.card F)^2 := Nat.mul_le_mul_right _ ht
    _ = 2*(Nat.card I*(Nat.card I-1)*(Nat.card F)^2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 2 (light_count_lower s hs R)

/-- For at least two copies, the construction itself satisfies a stronger
squared version of the proposed light-pair-weighted upper bound. -/
theorem incidence_square_le_light [Fintype A] [Fintype I] [Fintype F]
    (s : I → F) (hs : Function.Injective s) (R : A → F → Prop) (hI : 2 ≤ Nat.card I)
    (D : ℕ) (hD : ∀ b, Nat.card {a : Rows I A F // complete s R a b} ≤ D) :
    (Nat.card {p : Rows I A F × (I × F) // complete s R p.1 p.2})^2 ≤
      2*D^2*lightCount (complete s R) := by
  classical
  have he : Nat.card {p : Rows I A F × (I × F) // complete s R p.1 p.2} ≤ D*Nat.card (I × F) := by
    rw [edge_card_eq_cols]
    calc
      _ ≤ ∑ _b : I × F, D := sum_le_sum (fun b _ => hD b)
      _ = _ := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
  calc
    _ ≤ (D*Nat.card (I × F))^2 := Nat.pow_le_pow_left he 2
    _ = D^2*(Nat.card (I × F))^2 := mul_pow _ _ _
    _ ≤ D^2*(2*lightCount (complete s R)) := Nat.mul_le_mul_left _ (column_square_le_light s hs R hI)
    _ = _ := by ring

#print axioms cross_codegree_one
#print axioms light_count_lower
#print axioms incidence_square_le_light
end Erdos713ThetaTransversalLight
