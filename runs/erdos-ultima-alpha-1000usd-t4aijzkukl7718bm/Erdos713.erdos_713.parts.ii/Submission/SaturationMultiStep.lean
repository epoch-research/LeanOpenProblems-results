import FormalConjecturesUtil
import Submission.QuadraticSupportCenters
import Submission.SharpSaturatedWitnesses
import Submission.SaturationGrowth
import Submission.BoundedBackwardTransfer

/-! Bounded MULTI-step backward bounds on the same exact clone-saturated
near-order hosts. No quadratic support at the enlarged order is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713SaturationMultiStep
open Erdos713ExactCloneSaturation Erdos713QuadraticSupports
open Erdos713QuadraticSupportTangents Erdos713QuadraticSupportCenters
open Erdos713SaturationGrowth Erdos713BoundedBackwardTransfer
open Erdos713SharpSaturatedWitnesses Erdos713CloneSymm Erdos713Cloning
set_option maxHeartbeats 2000000

lemma eventual_multi_saturation {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a : ℝ}
    (ha : 1 < α) (ha0 : 0 < a) (hac : a < c*α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (R D : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ε : ℝ, 0 < ε → ε < η → QuadSupport (fun n => extremalNumber n H) ε n →
        ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
          n ≤ Fintype.card U ∧
          Fintype.card U ≤ n+(Fintype.card W+1)*(Fintype.card W)^2 ∧
          H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
          (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
          (∀ x, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet x) : ℝ)) ∧
          (∀ x, SingleFold H J x) ∧
          a*(Fintype.card U : ℝ)^(α-1) < (extremalNumber (Fintype.card U) H : ℝ)-
            (extremalNumber (Fintype.card U-1) H : ℝ) ∧
          ∀ r : ℕ, 1 ≤ r → r ≤ R →
            a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
              (extremalNumber (Fintype.card U) H : ℝ)-
                (extremalNumber (Fintype.card U-r) H : ℝ) := by
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  let A : ℝ := (L : ℝ)^2+L+2
  have hA : 0 < A := by dsimp [A]; positivity
  let E : ℝ := (L : ℝ)+((L : ℝ)+R)^2
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  let b : ℝ := (a+c*α)/2
  have hab : a < b := by dsimp [b]; linarith
  have hba : b < c*α := by dsimp [b]; linarith
  have hb : 0 < b := ha0.trans hab
  have hp : 0 < α-1 := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (max D (Fintype.card W) : ℝ)+1 ≤ b*(n : ℝ)^(α-1) :=
    (((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul_atTop hb).eventually_ge_atTop _
  refine ⟨1/(A+E+1),by positivity,?_⟩
  filter_upwards [eventually_support_lower h hba,eventually_shift_gap hab hp L,
    hlarge,eventually_gt_atTop (0 : ℕ),eventually_ge_atTop R] with n hlo hgap hNat hn hRn
  intro ε hε hεAE hrec
  have hAll : ε*(A+E+1) < 1 := (lt_div_iff₀ (by positivity : 0 < A+E+1)).mp hεAE
  have hεA : ε*A < 1 := by nlinarith only [hAll,mul_nonneg hε.le (show 0 ≤ E+1 by positivity)]
  have hεE : ε*E < 1 := by nlinarith only [hAll,mul_nonneg hε.le (show 0 ≤ A+1 by positivity)]
  let d : ℕ := ⌊b*(n : ℝ)^(α-1)⌋₊
  have hdle : (d : ℝ) ≤ b*(n : ℝ)^(α-1) := Nat.floor_le (by positivity)
  have hdgt : b*(n : ℝ)^(α-1) < (d : ℝ)+1 := Nat.lt_floor_add_one _
  have hdNat : max D (Fintype.card W) ≤ d := by
    exact_mod_cast (show (max D (Fintype.card W) : ℝ) ≤ d by linarith)
  have hdSlope : (d : ℝ) ≤ ε*(2*(n : ℝ)-1) := hdle.trans (hlo ε hrec).le
  obtain ⟨G,hopt,he⟩ := exists_ordinary_optimal H hEdge n
  have hcurv : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2+
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)+(2 : ℝ)) < 1 := by
    simpa [A,L] using hεA
  obtain ⟨U,hU,J,hnJ,hJupper,hfree,hE,hdeg,hfold,hback,hGrowth⟩ :=
    exact_saturated_with_growth H hH hn ((le_max_right D _).trans hdNat)
      G hopt he hε hrec hdSlope hcurv
  refine ⟨U,hU,J,hnJ,hJupper,hfree,hE,
    fun x => ((le_max_left D _).trans hdNat).trans (hdeg x),?_,hfold,?_,?_⟩
  · intro x
    have hcard : (Fintype.card U : ℝ) ≤ (n+L : ℕ) := by exact_mod_cast hJupper
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card U)) hcard hp.le
    have hmul := mul_le_mul_of_nonneg_left hpow ha0.le
    have hd : (d : ℝ) ≤ (Nat.card (J.neighborSet x) : ℝ) := by exact_mod_cast hdeg x
    linarith
  · have hcard : (Fintype.card U : ℝ) ≤ (n+L : ℕ) := by exact_mod_cast hJupper
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card U)) hcard hp.le
    have hmul := mul_le_mul_of_nonneg_left hpow ha0.le
    have hslope := hlo ε hrec
    linarith

  · intro r hr1 hrR
    have hrJ : r ≤ Fintype.card U := hrR.trans (hRn.trans hnJ)
    have hTransfer := backward_transfer (fun m => extremalNumber m H) hε.le hrec hnJ
      hJupper hrJ hrR hGrowth
    change (r : ℝ)*(ε*(2*(n : ℝ)-1))-ε*E ≤
      (extremalNumber (Fintype.card U) H : ℝ)-
        (extremalNumber (Fintype.card U-r) H : ℝ) at hTransfer
    have hcard : (Fintype.card U : ℝ) ≤ (n+L : ℕ) := by exact_mod_cast hJupper
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card U)) hcard hp.le
    have hmul := mul_le_mul_of_nonneg_left hpow ha0.le
    have hslope := hlo ε hrec
    have hs : a*(Fintype.card U : ℝ)^(α-1)+1 < ε*(2*(n : ℝ)-1) := by linarith
    have hrR1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hsmul := mul_lt_mul_of_pos_left hs (show (0 : ℝ) < r by exact_mod_cast hr1)
    nlinarith only [hsmul,hTransfer,hεE,hrR1]

/-- For EVERY sufficiently large reference order k, an exactly extremal,
fully clone-obstructed host exists in the relative window (1±delta)*k,
with any prescribed sharp minimum-degree coefficient below c*alpha. -/
theorem nearby_multi_saturated {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (hac : a < c*α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (R N D : ℕ) {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      N ≤ Fintype.card U ∧
      (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
      H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
      (∀ x, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet x) : ℝ)) ∧
      (∀ x, SingleFold H J x) ∧
          a*(Fintype.card U : ℝ)^(α-1) < (extremalNumber (Fintype.card U) H : ℝ)-
            (extremalNumber (Fintype.card U-1) H : ℝ) ∧
          ∀ r : ℕ, 1 ≤ r → r ≤ R →
            a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
              (extremalNumber (Fintype.card U) H : ℝ)-
                (extremalNumber (Fintype.card U-r) H : ℝ) := by
  let b := max a c
  have hb0 : 0 < b := hc.trans_le (le_max_right _ _)
  have hbc : b < c*α := max_lt hac (by nlinarith)
  obtain ⟨η,hη,hSat⟩ := eventual_multi_saturation H hH hEdge ha hb0 hbc h R D
  obtain ⟨M,hM⟩ := eventually_atTop.mp hSat
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  have hL : ∀ᶠ k : ℕ in atTop, (L : ℝ) < δ/2*k :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < δ/2)).eventually_gt_atTop _
  filter_upwards [nearby_supports ha ha2 hc h (max N M) 0 (δ := δ/2)
    (by positivity) hη,hL] with k hk hLk
  obtain ⟨n,ε,hnNM,_,hε,hεη,hSupport,_,hnlo,hnhi⟩ := hk
  obtain ⟨U,hU,J,hnJ,hJhi,hFree,hE,hD,hMin,hFold,hBack,hMulti⟩ :=
    hM n ((le_max_right N M).trans hnNM) ε hε hεη hSupport
  have hnJR : (n : ℝ) ≤ Fintype.card U := by exact_mod_cast hnJ
  have hJhiR : (Fintype.card U : ℝ) ≤ (n : ℝ)+L := by exact_mod_cast hJhi
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨U,hU,J,((le_max_left N M).trans hnNM).trans hnJ,?_,?_,hFree,hE,hD,?_,hFold,?_,?_⟩
  · nlinarith
  · linarith
  · intro x
    exact (mul_le_mul_of_nonneg_right (le_max_left a c)
      (Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card U)) _)).trans (hMin x)

  · exact (mul_le_mul_of_nonneg_right (le_max_left a c)
      (Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card U)) _)).trans_lt hBack

  · intro r hr1 hrR
    have hab : a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) ≤
        b*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left a c) (Nat.cast_nonneg r))
        (Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card U)) _)
    exact hab.trans_lt (hMulti r hr1 hrR)

#print axioms eventual_multi_saturation
#print axioms nearby_multi_saturated
end Erdos713SaturationMultiStep
