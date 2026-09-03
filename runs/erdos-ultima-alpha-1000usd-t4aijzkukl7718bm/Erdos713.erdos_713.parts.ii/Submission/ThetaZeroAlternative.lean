import FormalConjecturesUtil
import Submission.ThetaZeroPower
import Submission.ThetaLightPower

/-! An incidence alternative charged to zero-codegree pairs. -/
open Finset
namespace Erdos713ThetaZeroAlternative
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaZeroPower Erdos713ThetaZeroPairs Erdos713ThetaLightPower
variable {A B : Type*}
set_option maxHeartbeats 2000000

/-- The middle alternative records a small average pair codegree; it may
not be discarded in an unbalanced relation. -/
theorem zero_sixth_power_alternative [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (n D : ℕ) (hn : 0 < n)
    (hm : Fintype.card A ≤ n)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D) :
    Nat.card {p : A × B // R p.1 p.2} ≤ 200*n ∨
      (Nat.card {p : A × B // R p.1 p.2})^2 ≤ 640*n*(Fintype.card B)^2 ∨
      (Nat.card {p : A × B // R p.1 p.2})^6 ≤ 3932160000*n^4*D*(Fintype.card B)^2*(zeroSet R).card := by
  classical
  rw [edge_card_rows]
  let e := ∑ a : A, (row R a).card
  by_cases he : e ≤ 200*n
  · exact Or.inl he
  · apply Or.inr
    let r := e/(20*n)
    have hn20 : 0 < 20*n := by omega
    have hr : 6 ≤ r := by
      apply (Nat.le_div_iff_mul_le hn20).mpr
      omega
    have havg : 20*Fintype.card A*r ≤ e := by
      calc
        _ ≤ 20*n*r := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 20 hm)
        _ ≤ e := Nat.mul_div_le e (20*n)
    have hmod := Nat.mod_lt e hn20
    have hdiv : 20*n*r+e%(20*n) = e := Nat.div_add_mod e (20*n)
    have heR : e ≤ 40*n*r := by
      have hnR : n ≤ n*r := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith only [hdiv,hmod,hnR]
    by_cases hp : 16*(Fintype.card B)^2 ≤ r*e
    · apply Or.inr
      change e^6 ≤ _
      have hbound := pruned_zero_sixth_power hf r D hr hD havg hp
      have he4 := Nat.pow_le_pow_left heR 4
      calc
        e^6 = e^4*e^2 := by ring
        _ ≤ (40*n*r)^4*e^2 := Nat.mul_le_mul_right _ he4
        _ = (40*n)^4*(r^4*e^2) := by ring
        _ ≤ (40*n)^4*(1536*D*(zeroSet R).card*(Fintype.card B)^2) :=
          Nat.mul_le_mul_left _ hbound
        _ = 3932160000*n^4*D*(Fintype.card B)^2*(zeroSet R).card := by ring
    · apply Or.inl
      change e^2 ≤ _
      have hp' : r*e ≤ 16*(Fintype.card B)^2 := by omega
      calc
        e^2 = e*e := by ring
        _ ≤ (40*n*r)*e := Nat.mul_le_mul_right e heR
        _ = 40*n*(r*e) := by ring
        _ ≤ 40*n*(16*(Fintype.card B)^2) := Nat.mul_le_mul_left _ hp'
        _ = _ := by ring

#print axioms zero_sixth_power_alternative
end Erdos713ThetaZeroAlternative
