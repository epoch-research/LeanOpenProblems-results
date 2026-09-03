import FormalConjecturesUtil
import Submission.ApexThetaUpper
import Submission.ThetaSixthAlternative

/-! A ninth-power degree bound, using the legacy graph-helper chain. -/
open Finset SimpleGraph
namespace Erdos713GlobalThetaNinth
open Erdos713GlobalLight Erdos713GlobalTheta Erdos713ThetaCross
open Erdos713ConditionalThetaWeighted Erdos713ThetaSixthAlternative
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma ninth_from_alternative {n d D K e k : ℕ} (hdn : d ≤ n)
    (he : d*(d-1) ≤ e) (hD : D ≤ K*d) (hk : k ≤ K*d)
    (halt : e ≤ 200*n ∨ e^2 ≤ 640*n*k^2 ∨ e^6 ≤ 11796480000*n^5*D*k^2) :
    d^9 ≤ 1000000000000000*(K+1)^8*n^5 := by
  have hK1 : 1 ≤ (K+1)^8 := one_le_pow₀ (by omega)
  by_cases hd : 2 ≤ d
  · have hsub : d-1+1 = d := Nat.sub_add_cancel (by omega)
    have hd2 : d^2 ≤ 2*e := by nlinarith
    rcases halt with hl | hm | hh
    · have hdsq : d^2 ≤ 400*n := by omega
      have hd8 := Nat.pow_le_pow_left hdsq 4
      calc
        d^9 = (d^2)^4*d := by ring
        _ ≤ (400*n)^4*n := Nat.mul_le_mul hd8 hdn
        _ = 25600000000*n^5 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith only [hK1])
    · have hd4 := Nat.pow_le_pow_left hd2 2
      have hk2 := Nat.pow_le_pow_left hk 2
      have he2 : e^2 ≤ 640*n*(K*d)^2 := hm.trans (Nat.mul_le_mul_left _ hk2)
      have hc : d^2*d^2 ≤ (2560*K^2*n)*d^2 := by
        calc
          _ = (d^2)^2 := by ring
          _ ≤ (2*e)^2 := hd4
          _ = 4*e^2 := by ring
          _ ≤ 4*(640*n*(K*d)^2) := Nat.mul_le_mul_left _ he2
          _ = _ := by ring
      have hdsq : d^2 ≤ 2560*K^2*n := Nat.le_of_mul_le_mul_right hc (by positivity)
      have hd8 := Nat.pow_le_pow_left hdsq 4
      have hK8 := Nat.pow_le_pow_left (show K ≤ K+1 by omega) 8
      calc
        d^9 = (d^2)^4*d := by ring
        _ ≤ (2560*K^2*n)^4*n := Nat.mul_le_mul hd8 hdn
        _ = 42949672960000*K^8*n^5 := by ring
        _ ≤ 1000000000000000*(K+1)^8*n^5 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by decide) hK8)
    · have hd12 := Nat.pow_le_pow_left hd2 6
      have hk2 := Nat.pow_le_pow_left hk 2
      have he6 : e^6 ≤ 11796480000*n^5*(K*d)*(K*d)^2 :=
        hh.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) hk2)
      have hb : d^9*d^3 ≤ (754974720000*K^3*n^5)*d^3 := by
        calc
          _ = (d^2)^6 := by ring
          _ ≤ (2*e)^6 := hd12
          _ = 64*e^6 := by ring
          _ ≤ 64*(11796480000*n^5*(K*d)*(K*d)^2) := Nat.mul_le_mul_left _ he6
          _ = _ := by ring
      have hcancel := Nat.le_of_mul_le_mul_right hb (by positivity : 0 < d^3)
      have hK3 : K^3 ≤ (K+1)^8 :=
        (Nat.pow_le_pow_left (show K ≤ K+1 by omega) 3).trans
          (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 8))
      exact hcancel.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by decide) hK3))
  · interval_cases d
    · simp
    · have hn5 : 1 ≤ n^5 := one_le_pow₀ (by omega)
      simpa only [one_pow] using hn5.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- The row maximum now controls the number of columns in the chosen link;
the column maximum controls its column degrees. -/
theorem ninth_power [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (n d D K : ℕ) (hn : 0 < n)
    (hAB : Fintype.card B ≤ Fintype.card A) (hAn : Fintype.card A ≤ n)
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hRowMax : ∀ a, Nat.card {b // R a b} ≤ D)
    (hColMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d) :
    d^9 ≤ 1000000000000000*(K+1)^8*n^5 := by
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
    have hh' := hColMax b.val
    omega
  have hm : Fintype.card {x : A // x ≠ a} ≤ n :=
    (Fintype.card_subtype_le _).trans hAn
  have hAlt := sixth_power_alternative (no_theta_links hFree a) n D hn hm htR hCap
  have hlo := link_incidence_lower R a d (hrows a) hcols
  have hdB : d ≤ Fintype.card B := (hrows a).trans (by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (R a))
  have hk : Fintype.card {b // R a b} ≤ K*d := by
    simpa only [Nat.card_eq_fintype_card] using (hRowMax a).trans hRatio
  exact ninth_from_alternative (hdB.trans (hAB.trans hAn)) hlo hRatio hk hAlt

#print axioms ninth_from_alternative
#print axioms ninth_power
end Erdos713GlobalThetaNinth
