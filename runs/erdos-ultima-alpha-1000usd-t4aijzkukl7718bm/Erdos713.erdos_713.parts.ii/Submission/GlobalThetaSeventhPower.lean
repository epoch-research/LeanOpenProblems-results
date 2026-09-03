import FormalConjecturesUtil
import Submission.ThetaLightPower
import Submission.ConditionalThetaWeighted

/-! An unconditional finite seventh-power degree inequality for the
apex-theta pattern. The previously proposed capped estimate is NOT used. -/
open Finset SimpleGraph
namespace Erdos713GlobalThetaSeventh
open Erdos713GlobalLight Erdos713GlobalTheta Erdos713ThetaCross
open Erdos713ConditionalThetaWeighted Erdos713ThetaLightPower
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma seventh_from_alternative {n d D K e : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (he : d*(d-1) ≤ e) (hD : D ≤ K*d)
    (halt : e ≤ 200*n ∨ e^4 ≤ 18432000*n^4*D) :
    d^7 ≤ 294912000*(K+1)*n^4 := by
  by_cases hd : 2 ≤ d
  · have hsub : d-1+1 = d := Nat.sub_add_cancel (by omega)
    have hd2 : d^2 ≤ 2*e := by nlinarith
    rcases halt with hl | hh
    · have hdsq : d^2 ≤ 400*n := by omega
      have hd6 := Nat.pow_le_pow_left hdsq 3
      calc
        d^7 = (d^2)^3*d := by ring
        _ ≤ (400*n)^3*n := Nat.mul_le_mul hd6 hdn
        _ = 64000000*n^4 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · have hd8 := Nat.pow_le_pow_left hd2 4
      have heD := Nat.mul_le_mul_left (18432000*n^4) hD
      have hb : d^7*d ≤ (294912000*K*n^4)*d := by
        calc
          _ = (d^2)^4 := by ring
          _ ≤ (2*e)^4 := hd8
          _ = 16*e^4 := by ring
          _ ≤ 16*(18432000*n^4*D) := Nat.mul_le_mul_left 16 hh
          _ ≤ 16*(18432000*n^4*(K*d)) := Nat.mul_le_mul_left 16 heD
          _ = _ := by ring
      have hcancel := Nat.le_of_mul_le_mul_right hb (by omega : 0 < d)
      exact hcancel.trans (by gcongr; omega)
  · interval_cases d
    · simp
    · have hn4 : 1 ≤ n^4 := Nat.one_le_pow _ _ (by omega)
      simpa only [one_pow] using hn4.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- Choose the root on the larger shore. The whole-host light-pair budget,
theta exclusion in that link, and the degree bounds concern the SAME host. -/
theorem seventh_power [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (n d D K : ℕ) (hn : 0 < n)
    (hAB : Fintype.card B ≤ Fintype.card A) (hAn : Fintype.card A ≤ n)
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d) :
    d^7 ≤ 294912000*(K+1)*n^4 := by
  classical
  obtain ⟨a,ha⟩ := exists_row_with_few_light_pairs R 3
  have ht : (lightPairs R 3 a).card ≤ 3*n := by
    have hab2 := Nat.pow_le_pow_left hAB 2
    have hprod : Fintype.card A*(lightPairs R 3 a).card ≤ Fintype.card A*(3*Fintype.card A) := by
      calc
        _ ≤ 3*(Fintype.card B)^2 := ha
        _ ≤ 3*(Fintype.card A)^2 := Nat.mul_le_mul_left 3 hab2
        _ = _ := by ring
    have hh := Nat.le_of_mul_le_mul_left hprod (Fintype.card_pos (α := A))
    omega
  have htR : lightCount (link R a) ≤ 3*n := by rwa [link_lightCount]
  have hCap (b : {b // R a b}) : Nat.card {x : {x : A // x ≠ a} // link R a x b} ≤ D := by
    have hh := link_column_add_one R a b
    have hh' := hMax b.val
    omega
  have hm : Fintype.card {x : A // x ≠ a} ≤ n :=
    (Fintype.card_subtype_le _).trans hAn
  have hAlt := fourth_power_alternative (no_theta_links hFree a) n D hn hm htR hCap
  have hlo := link_incidence_lower R a d (hrows a) hcols
  have hdB : d ≤ Fintype.card B := (hrows a).trans (by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (R a))
  exact seventh_from_alternative hn (hdB.trans (hAB.trans hAn)) hlo hRatio hAlt

#print axioms seventh_from_alternative
#print axioms seventh_power
end Erdos713GlobalThetaSeventh
