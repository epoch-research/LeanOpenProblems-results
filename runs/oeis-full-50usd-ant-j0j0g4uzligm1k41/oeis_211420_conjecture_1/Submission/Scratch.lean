import Mathlib
open Finset
set_option maxHeartbeats 2000000

theorem keyfloor_base (q s t : ℤ) (hq : 0 < q) (hs0 : 0 ≤ s) (hsq : s < q)
    (ht0 : 0 ≤ t) (htq : t < q) :
    (2*s)/q + (3*s)/q + (4*s - t)/q ≤ (8*t)/q + s/q + (8*s - 2*t)/q := by
  have hsq0 : s / q = 0 := Int.ediv_eq_zero_of_lt hs0 hsq
  rw [hsq0, add_zero]
  rw [show (2*s)/q + (3*s)/q + (4*s - t)/q ≤ (8*t)/q + (8*s - 2*t)/q
        ↔ (2*s)/q + (3*s)/q + (4*s - t)/q - (8*s - 2*t)/q ≤ (8*t)/q from by omega,
     Int.le_ediv_iff_mul_le hq]
  set a2 := (2*s)/q with ha2
  set a3 := (3*s)/q with ha3
  set a4 := (4*s - t)/q with ha4
  set a82 := (8*s - 2*t)/q with ha82
  have e2 := Int.mul_ediv_add_emod (2*s) q
  have e3 := Int.mul_ediv_add_emod (3*s) q
  have e4 := Int.mul_ediv_add_emod (4*s - t) q
  have e82 := Int.mul_ediv_add_emod (8*s - 2*t) q
  have n2 := Int.emod_nonneg (2*s) (ne_of_gt hq)
  have n3 := Int.emod_nonneg (3*s) (ne_of_gt hq)
  have n4 := Int.emod_nonneg (4*s - t) (ne_of_gt hq)
  have n82 := Int.emod_nonneg (8*s - 2*t) (ne_of_gt hq)
  have l2 := Int.emod_lt_of_pos (2*s) hq
  have l3 := Int.emod_lt_of_pos (3*s) hq
  have l4 := Int.emod_lt_of_pos (4*s - t) hq
  have l82 := Int.emod_lt_of_pos (8*s - 2*t) hq
  rw [← ha2] at e2; rw [← ha3] at e3; rw [← ha4] at e4; rw [← ha82] at e82
  have b2l : 0 ≤ a2 := by rw [ha2]; apply Int.ediv_nonneg (by linarith) (le_of_lt hq)
  have b2u : a2 ≤ 1 := by rw [ha2, Int.ediv_le_iff_le_mul hq]; nlinarith
  have b3l : 0 ≤ a3 := by rw [ha3]; apply Int.ediv_nonneg (by linarith) (le_of_lt hq)
  have b3u : a3 ≤ 2 := by rw [ha3, Int.ediv_le_iff_le_mul hq]; nlinarith
  have b4l : -1 ≤ a4 := by rw [ha4, Int.le_ediv_iff_mul_le hq]; nlinarith
  have b4u : a4 ≤ 3 := by rw [ha4, Int.ediv_le_iff_le_mul hq]; nlinarith
  have rel1 : 2*a4 ≤ a82 := by nlinarith
  have rel2 : a82 ≤ 2*a4 + 1 := by nlinarith
  clear_value a2 a3 a4 a82
  interval_cases a2 <;> interval_cases a3 <;> interval_cases a4 <;> interval_cases a82 <;> omega

theorem keyfloor_int (q n r : ℤ) (hq : 0 < q) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    (2*n)/q + (3*n)/q + (4*n - r)/q ≤ (8*r)/q + n/q + (8*n - 2*r)/q := by
  set A := n / q with hA
  set s := n % q with hs
  set B := r / q with hB
  set t := r % q with ht
  have hmodn : s + q * A = n := by rw [hs, hA]; exact Int.emod_add_ediv n q
  have hmodr : t + q * B = r := by rw [ht, hB]; exact Int.emod_add_ediv r q
  have hns : n = q * A + s := by omega
  have hrt : r = q * B + t := by omega
  have hs0 : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg n (ne_of_gt hq)
  have hsq : s < q := by rw [hs]; exact Int.emod_lt_of_pos n hq
  have ht0 : 0 ≤ t := by rw [ht]; exact Int.emod_nonneg r (ne_of_gt hq)
  have htq : t < q := by rw [ht]; exact Int.emod_lt_of_pos r hq
  have hB0 : 0 ≤ B := by rw [hB]; exact Int.ediv_nonneg hr (le_of_lt hq)
  have r2 : (2*n)/q = 2*A + (2*s)/q := by
    rw [show 2*n = 2*s + q*(2*A) by rw [hns]; ring, Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r3 : (3*n)/q = 3*A + (3*s)/q := by
    rw [show 3*n = 3*s + q*(3*A) by rw [hns]; ring, Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r4 : (4*n - r)/q = (4*A - B) + (4*s - t)/q := by
    rw [show 4*n - r = (4*s - t) + q*(4*A - B) by rw [hns, hrt]; ring,
       Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r8r : (8*r)/q = 8*B + (8*t)/q := by
    rw [show 8*r = 8*t + q*(8*B) by rw [hrt]; ring, Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r82 : (8*n - 2*r)/q = (8*A - 2*B) + (8*s - 2*t)/q := by
    rw [show 8*n - 2*r = (8*s - 2*t) + q*(8*A - 2*B) by rw [hns, hrt]; ring,
       Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have hbase := keyfloor_base q s t hq hs0 hsq ht0 htq
  rw [r2, r3, r4, r8r, r82]
  have hsq0 : s / q = 0 := Int.ediv_eq_zero_of_lt hs0 hsq
  rw [hsq0, add_zero] at hbase
  linarith
