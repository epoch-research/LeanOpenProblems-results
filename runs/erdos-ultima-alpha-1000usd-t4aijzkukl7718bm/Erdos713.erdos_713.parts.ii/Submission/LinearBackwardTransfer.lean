import FormalConjecturesUtil
import Submission.BoundedBackwardTransfer

/-! Keep the r-dependent quadratic loss, instead of bounding it by a
constant for a fixed number of backward steps. -/
namespace Erdos713LinearBackwardTransfer
open Erdos713ExactCloneSaturation
set_option maxHeartbeats 2000000

lemma backward_transfer (f : ℕ → ℕ) {ε : ℝ} {n m L r : ℕ}
    (hε : 0 ≤ ε) (hrec : QuadSupport f ε n) (hnm : n ≤ m) (hmL : m ≤ n+L)
    (hrm : r ≤ m)
    (hgrowth : ε*(2*(n : ℝ)-1)*(m-n : ℕ) ≤ (f m : ℝ)-(f n : ℝ)) :
    (r : ℝ)*(ε*(2*(n : ℝ)-1)-ε*r)-ε*((L : ℝ)^2+L) ≤
      (f m : ℝ)-(f (m-r) : ℝ) := by
  let t : ℕ := m-n
  have htL : t ≤ L := by dsimp [t]; omega
  have hm : (m : ℝ) = (n : ℝ)+t := by dsimp [t]; rw [Nat.cast_sub hnm]; ring
  have hmr : ((m-r : ℕ) : ℝ) = (n : ℝ)+t-r := by rw [Nat.cast_sub hrm,hm]
  have hrec' := hrec (m-r)
  rw [hmr] at hrec'
  change ε*(2*(n : ℝ)-1)*(t : ℝ) ≤ (f m : ℝ)-(f n : ℝ) at hgrowth
  have hlocal : (r : ℝ)*(ε*(2*(n : ℝ)-1)-ε*r)-ε*((t : ℝ)^2+t) ≤
      (f m : ℝ)-(f (m-r) : ℝ) := by
    have hr := mul_nonneg hε (Nat.cast_nonneg (α := ℝ) r)
    have hrt := mul_nonneg hr (Nat.cast_nonneg (α := ℝ) t)
    nlinarith only [hrec',hgrowth,hr,hrt]
  have herr : (t : ℝ)^2+t ≤ (L : ℝ)^2+L := by
    have htl : (t : ℝ) ≤ L := by exact_mod_cast htL
    nlinarith only [htl,Nat.cast_nonneg (α := ℝ) t,Nat.cast_nonneg (α := ℝ) L]
  have hmul := mul_le_mul_of_nonneg_left herr hε
  linarith

lemma slope_after_loss {ε s r b z p : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) (hz : 0 < z)
    (hbudget : b*r ≤ (b-z)*s) (hslope : b*p < ε*s) : z*p < ε*s-ε*r := by
  have h1 := mul_le_mul_of_nonneg_left hbudget hε
  have h2 := mul_lt_mul_of_pos_left hslope hz
  apply (mul_lt_mul_iff_right₀ hb).mp
  show b*(z*p) < b*(ε*s-ε*r)
  nlinarith only [h1,h2]

lemma window_pos {b z : ℝ} (hb : 0 < b) (hz : 0 < z) (hzb : z < b) :
    0 < (b-z)/(2*b) ∧ (b-z)/(2*b) < 1 := by
  constructor
  · exact div_pos (sub_pos.mpr hzb) (by positivity)
  · apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith

lemma window_budget {b z n m r : ℝ} (hb : 0 < b) (hzb : z ≤ b)
    (hn : 1 ≤ n) (hm : m ≤ 2*n) (hr : r ≤ (b-z)/(2*b)*m) :
    b*r ≤ (b-z)*(2*n-1) := by
  have hθ : 0 ≤ (b-z)/(2*b) := div_nonneg (sub_nonneg.mpr hzb) (by positivity)
  calc
    b*r ≤ b*((b-z)/(2*b)*(2*n)) :=
      mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_left hm hθ)) hb.le
    _ = (b-z)*n := by field_simp
    _ ≤ (b-z)*(2*n-1) := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hzb)

#print axioms backward_transfer
#print axioms slope_after_loss
#print axioms window_budget
end Erdos713LinearBackwardTransfer
