import FormalConjecturesUtil
import Submission.FlatSupportContacts

/-! A bounded enlargement retaining the supported linear growth inherits
bounded multi-step backward inequalities, up to an explicit curvature loss. -/
open Finset
namespace Erdos713BoundedBackwardTransfer
open Erdos713ExactCloneSaturation
set_option maxHeartbeats 2000000

lemma square_error {t r L M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hL : t ≤ L) (hM : r ≤ M) : t+(t-r)^2 ≤ L+(L+M)^2 := by
  have hlo : -(L+M) ≤ t-r := by linarith
  have hhi : t-r ≤ L+M := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ (L+M)+(t-r) by linarith)
  nlinarith only [hp,hL]

/-- No integrality of the contact slope and no differentiability of f are
needed. The error bound is deliberately coarse and uniform for r<=M. -/
lemma backward_transfer (f : ℕ → ℕ) {ε : ℝ} {n m L M r : ℕ}
    (hε : 0 ≤ ε) (hrec : QuadSupport f ε n) (hnm : n ≤ m) (hmL : m ≤ n+L)
    (hrm : r ≤ m) (hrM : r ≤ M)
    (hgrowth : ε*(2*(n : ℝ)-1)*(m-n : ℕ) ≤ (f m : ℝ)-(f n : ℝ)) :
    (r : ℝ)*(ε*(2*(n : ℝ)-1))-ε*((L : ℝ)+((L : ℝ)+M)^2) ≤
      (f m : ℝ)-(f (m-r) : ℝ) := by
  let t : ℕ := m-n
  have htL : t ≤ L := by dsimp [t]; omega
  have hm : (m : ℝ) = (n : ℝ)+t := by dsimp [t]; rw [Nat.cast_sub hnm]; ring
  have hmr : ((m-r : ℕ) : ℝ) = (n : ℝ)+t-r := by rw [Nat.cast_sub hrm,hm]
  have hrec' := hrec (m-r)
  rw [hmr] at hrec'
  change ε*(2*(n : ℝ)-1)*(t : ℝ) ≤ (f m : ℝ)-(f n : ℝ) at hgrowth
  have hlocal : (r : ℝ)*(ε*(2*(n : ℝ)-1))-ε*((t : ℝ)+((t : ℝ)-r)^2) ≤
      (f m : ℝ)-(f (m-r) : ℝ) := by
    have hr := mul_nonneg hε (Nat.cast_nonneg (α := ℝ) r)
    nlinarith only [hrec',hgrowth,hr]
  have herr := square_error (Nat.cast_nonneg (α := ℝ) t) (Nat.cast_nonneg (α := ℝ) r)
    (show (t : ℝ) ≤ L by exact_mod_cast htL) (show (r : ℝ) ≤ M by exact_mod_cast hrM)
  have hmul := mul_le_mul_of_nonneg_left herr hε
  linarith

#print axioms backward_transfer
end Erdos713BoundedBackwardTransfer
