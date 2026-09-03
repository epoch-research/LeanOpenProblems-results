import FormalConjecturesUtil
import Submission.ThetaPrunedPower

/-! A fourth-power incidence bound with a light-pair budget. -/
open Finset
namespace Erdos713ThetaLightPower
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaSplit Erdos713ThetaPrunedPower
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma edge_card_rows [Fintype A] [Fintype B] (R : A → B → Prop) :
    Nat.card {p : A × B // R p.1 p.2} = ∑ a : A, (row R a).card := by
  classical
  rw [edge_card_eq_rows]
  simp only [row,Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- With at most n rows and at most 3n ordered light pairs, either the
incidence count is linear in n or its fourth power is bounded by n^4*D. -/
theorem fourth_power_alternative [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (n D : ℕ) (hn : 0 < n)
    (hm : Fintype.card A ≤ n) (ht : lightCount R ≤ 3*n)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D) :
    Nat.card {p : A × B // R p.1 p.2} ≤ 200*n ∨
      (Nat.card {p : A × B // R p.1 p.2})^4 ≤ 18432000*n^4*D := by
  classical
  rw [edge_card_rows]
  let e := ∑ a : A, (row R a).card
  by_cases he : e ≤ 200*n
  · exact Or.inl he
  · apply Or.inr
    change e^4 ≤ _
    let r := e/(20*n)
    have hn20 : 0 < 20*n := by omega
    have hr : 6 ≤ r := by
      apply (Nat.le_div_iff_mul_le hn20).mpr
      omega
    have havg : 20*Fintype.card A*r ≤ e := by
      calc
        _ ≤ 20*n*r := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 20 hm)
        _ ≤ e := Nat.mul_div_le e (20*n)
    have hlight : 16*lightCount R ≤ r*e := by
      have h1 : 16*lightCount R ≤ 48*n := by omega
      have h2 : 48*n ≤ e := by omega
      exact h1.trans (h2.trans (Nat.le_mul_of_pos_left _ (by omega)))
    have hp : r^3*e ≤ 96*D*lightCount R := pruned_power hf r D hr hD havg hlight
    have hmod := Nat.mod_lt e hn20
    have hdiv : 20*n*r+e%(20*n) = e := Nat.div_add_mod e (20*n)
    have heR : e ≤ 40*n*r := by
      have hnR : n ≤ n*r := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith only [hdiv,hmod,hnR]
    have he3 := Nat.pow_le_pow_left heR 3
    have he4 : e^4 ≤ 6144000*n^3*D*lightCount R := by
      calc
        e^4 = e^3*e := by ring
        _ ≤ (40*n*r)^3*e := Nat.mul_le_mul_right e he3
        _ = (40*n)^3*(r^3*e) := by ring
        _ ≤ (40*n)^3*(96*D*lightCount R) := Nat.mul_le_mul_left _ hp
        _ = _ := by ring
    calc
      _ ≤ 6144000*n^3*D*lightCount R := he4
      _ ≤ 6144000*n^3*D*(3*n) := Nat.mul_le_mul_left _ ht
      _ = _ := by ring

#print axioms edge_card_rows
#print axioms fourth_power_alternative
end Erdos713ThetaLightPower
