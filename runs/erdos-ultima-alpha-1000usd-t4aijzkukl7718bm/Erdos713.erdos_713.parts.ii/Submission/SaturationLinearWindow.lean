import FormalConjecturesUtil
import Submission.QuadraticSupportCenters
import Submission.SharpSaturatedWitnesses
import Submission.SaturationGrowth
import Submission.LinearBackwardTransfer

/-! Sharp backward bounds on a LINEAR window of steps at the selected
exact clone-saturated orders. No support at the output order is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713SaturationLinearWindow
open Erdos713ExactCloneSaturation Erdos713QuadraticSupportTangents
open Erdos713QuadraticSupportCenters Erdos713SaturationGrowth
open Erdos713SharpSaturatedWitnesses Erdos713CloneSymm Erdos713Cloning
open Erdos713LinearBackwardTransfer
set_option maxHeartbeats 2000000

lemma eventual_linear_saturation {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a : ℝ}
    (ha : 1 < α) (ha0 : 0 < a) (hac : a < c*α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ θ η : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < η ∧ ∀ D : ℕ, ∀ᶠ n : ℕ in atTop,
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
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ θ*Fintype.card U →
            a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
              (extremalNumber (Fintype.card U) H : ℝ)-
                (extremalNumber (Fintype.card U-r) H : ℝ) := by
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  let A : ℝ := (L : ℝ)^2+L+2
  have hA : 0 < A := by dsimp [A]; positivity
  let b : ℝ := (a+c*α)/2
  let z : ℝ := (a+b)/2
  have hab : a < b := by dsimp [b]; linarith
  have hba : b < c*α := by dsimp [b]; linarith
  have haz : a < z := by dsimp [z]; linarith
  have hzb : z < b := by dsimp [z]; linarith
  have hb : 0 < b := ha0.trans hab
  have hz : 0 < z := ha0.trans haz
  have hθ := window_pos hb hz hzb
  refine ⟨(b-z)/(2*b),1/A,hθ.1,hθ.2,by positivity,?_⟩
  intro D
  have hp : 0 < α-1 := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (max D (Fintype.card W) : ℝ)+1 ≤ b*(n : ℝ)^(α-1) :=
    (((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul_atTop hb).eventually_ge_atTop _
  filter_upwards [eventually_support_lower h hba,eventually_shift_gap haz hp L,
    hlarge,eventually_gt_atTop (0 : ℕ),eventually_ge_atTop L] with n hlo hgap hNat hn hLn
  intro ε hε hεA hrec
  have hFlat : ε*A < 1 := (lt_div_iff₀ hA).mp hεA
  have hError : ε*((L : ℝ)^2+L) < 1 := by
    dsimp only [A] at hFlat
    nlinarith only [hFlat,hε]
  let d : ℕ := ⌊b*(n : ℝ)^(α-1)⌋₊
  have hdle : (d : ℝ) ≤ b*(n : ℝ)^(α-1) := Nat.floor_le (by positivity)
  have hdgt : b*(n : ℝ)^(α-1) < (d : ℝ)+1 := Nat.lt_floor_add_one _
  have hdNat : max D (Fintype.card W) ≤ d := by
    exact_mod_cast (show (max D (Fintype.card W) : ℝ) ≤ d by linarith)
  have hdSlope : (d : ℝ) ≤ ε*(2*(n : ℝ)-1) := hdle.trans (hlo ε hrec).le
  obtain ⟨G,hopt,he⟩ := exists_ordinary_optimal H hEdge n
  have hcurv : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2+
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)+(2 : ℝ)) < 1 := by
    simpa [A,L] using hFlat
  obtain ⟨U,hU,J,hnJ,hJupper,hfree,hE,hdeg,hfold,hback,hGrowth⟩ :=
    exact_saturated_with_growth H hH hn ((le_max_right D _).trans hdNat)
      G hopt he hε hrec hdSlope hcurv
  have hcard : (Fintype.card U : ℝ) ≤ (n+L : ℕ) := by exact_mod_cast hJupper
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card U)) hcard hp.le
  have hmul := mul_le_mul_of_nonneg_left hpow ha0.le
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm2n : (Fintype.card U : ℝ) ≤ 2*(n : ℝ) := by
    exact_mod_cast (show Fintype.card U ≤ 2*n by omega)
  have hgapB : a*((n+L : ℕ) : ℝ)^(α-1)+1 < b*(n : ℝ)^(α-1) :=
    hgap.trans (mul_lt_mul_of_pos_right hzb (Real.rpow_pos_of_pos hnR _))
  refine ⟨U,hU,J,hnJ,hJupper,hfree,hE,
    fun x => ((le_max_left D _).trans hdNat).trans (hdeg x),?_,hfold,?_,?_⟩
  · intro x
    have hd : (d : ℝ) ≤ (Nat.card (J.neighborSet x) : ℝ) := by exact_mod_cast hdeg x
    linarith
  · have hslope := hlo ε hrec
    linarith
  · intro r hr1 hrθ
    have hrJ : r ≤ Fintype.card U := by
      have hmulθ := mul_le_mul_of_nonneg_right hθ.2.le (Nat.cast_nonneg (α := ℝ) (Fintype.card U))
      have hrR : (r : ℝ) ≤ (Fintype.card U : ℝ) :=
        hrθ.trans (by simpa only [one_mul] using hmulθ)
      exact_mod_cast hrR
    have hTransfer := backward_transfer (fun m => extremalNumber m H) hε.le hrec hnJ
      hJupper hrJ hGrowth
    have hbudget := window_budget hb hzb.le hnR1 hm2n hrθ
    have hSlope := slope_after_loss hε.le hb hz hbudget (hlo ε hrec)
    have hs : a*(Fintype.card U : ℝ)^(α-1)+1 < ε*(2*(n : ℝ)-1)-ε*r := by linarith
    have hrR1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hsmul := mul_lt_mul_of_pos_left hs (show (0 : ℝ) < r by exact_mod_cast hr1)
    change (r : ℝ)*(ε*(2*(n : ℝ)-1)-ε*r)-ε*((L : ℝ)^2+L) ≤ _ at hTransfer
    nlinarith only [hsmul,hTransfer,hError,hrR1]

/-- The positive fraction theta is fixed BEFORE size, degree, and relative
order-window targets. All backward steps through theta times the OUTPUT
order are covered simultaneously. -/
theorem nearby_linear_saturated {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a) (hac : a < c*α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ N D : ℕ, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
        N ≤ Fintype.card U ∧
        (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
        H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
        (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
        (∀ x, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet x) : ℝ)) ∧
        (∀ x, SingleFold H J x) ∧
        a*(Fintype.card U : ℝ)^(α-1) < (extremalNumber (Fintype.card U) H : ℝ)-
          (extremalNumber (Fintype.card U-1) H : ℝ) ∧
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ θ*Fintype.card U →
          a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
            (extremalNumber (Fintype.card U) H : ℝ)-
              (extremalNumber (Fintype.card U-r) H : ℝ) := by
  obtain ⟨θ,η,hθ0,hθ1,hη,hSat⟩ := eventual_linear_saturation H hH hEdge ha ha0 hac h
  refine ⟨θ,hθ0,hθ1,?_⟩
  intro N D δ hd
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hSat D)
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
  refine ⟨U,hU,J,((le_max_left N M).trans hnNM).trans hnJ,?_,?_,hFree,hE,hD,hMin,hFold,hBack,hMulti⟩
  · nlinarith
  · linarith

#print axioms eventual_linear_saturation
#print axioms nearby_linear_saturated
end Erdos713SaturationLinearWindow
