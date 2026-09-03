import FormalConjecturesUtil
import Submission.ExactCloneSaturation

/-! Integer contacts under a flat quadratic support retain a backward
increment bound. No support at the shifted order is asserted. -/
namespace Erdos713FlatSupportContacts
open Erdos713ExactCloneSaturation
set_option maxHeartbeats 2000000

lemma support_backward (f : ℕ → ℕ) {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hrec : QuadSupport f ε n) :
    ε*(2*(n : ℝ)-1) ≤ (f n : ℝ)-(f (n-1) : ℝ) := by
  have hh := hrec (n-1)
  have hnm : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hnm] at hh
  nlinarith only [hh]

lemma integer_contact_upper (f : ℕ → ℕ) {n t d : ℕ} {ε : ℝ}
    (hrec : QuadSupport f ε n) (hd : ε*(2*(n : ℝ)-1) ≤ (d : ℝ))
    (hflat : ε*((t : ℝ)^2+t) < 1) :
    f (n+t) ≤ f n+d*t := by
  have hr := hrec (n+t)
  push_cast at hr
  have hm := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  have hu : (f (n+t) : ℝ) < (f n : ℝ)+(d : ℝ)*t+1 := by nlinarith only [hr,hm,hflat]
  have huNat : f (n+t) < f n+d*t+1 := by exact_mod_cast hu
  omega

/-- A shifted integer contact with the supporting lower line has a large
backward increment, even though it need not itself be a support order. -/
lemma backward_at_contact (f : ℕ → ℕ) {n m L d : ℕ} {ε : ℝ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hrec : QuadSupport f ε n)
    (hd : ε*(2*(n : ℝ)-1) ≤ (d : ℝ))
    (hflat : ε*((L : ℝ)^2+L) < 1) (hnm : n ≤ m) (hm : m ≤ n+L)
    (hcontact : f m = f n+d*(m-n)) :
    ε*(2*(n : ℝ)-1) ≤ (f m : ℝ)-(f (m-1) : ℝ) := by
  by_cases he : m = n
  · subst m
    exact support_backward f hn hrec
  · let t := m-1-n
    have ht : t ≤ L := by dsimp [t]; omega
    have hnt : n+t = m-1 := by dsimp [t]; omega
    have htn : m-n = t+1 := by dsimp [t]; omega
    have htR : (t : ℝ) ≤ L := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have hflatT : ε*((t : ℝ)^2+t) < 1 := by
      apply lt_of_le_of_lt _ hflat
      apply mul_le_mul_of_nonneg_left _ hε
      nlinarith
    have hu := integer_contact_upper f hrec hd hflatT
    rw [hnt] at hu
    have hstep : f (m-1)+d ≤ f m := by rw [hcontact,htn]; nlinarith only [hu]
    have hstepR : (f (m-1) : ℝ)+(d : ℝ) ≤ (f m : ℝ) := by exact_mod_cast hstep
    linarith

#print axioms backward_at_contact
end Erdos713FlatSupportContacts
