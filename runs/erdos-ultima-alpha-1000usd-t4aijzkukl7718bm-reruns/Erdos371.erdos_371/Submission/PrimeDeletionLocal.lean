import FormalConjecturesUtil
import Submission.PrimeDeletion

/-! Infinitely many local failures of pointwise affine-deletion sign bounds.
These do not refute a cumulative sign bound or the density conjecture. -/

namespace Erdos371PrimeDeletionLocal

open Finset Erdos371PrimeDeletion

noncomputable def rightLocal (n : ℕ) : ℝ := rightDeleted (n + 1).primeFactors n

noncomputable def leftLocal (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, Erdos371PrimeDeletion.compare (P (n / p)) (P (n + 1))

lemma height_of_small_mul {a q : ℕ} (ha : 0 < a) (haq : a ≤ q) (hq : q.Prime) :
    P (a * q) = q := by
  rw [P, Nat.maxPrimeFac_mul ha.ne' hq.ne_zero, hq.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.maxPrimeFac_le.trans haq)

lemma height_bounds_of_seven_dvd {m q : ℕ} (hm : 0 < m) (hq : 7 < q)
    (hsmall : m < q * 7) (hd : 7 ∣ m) : 7 ≤ P m ∧ P m < q := by
  have hquot : 0 < m / 7 := Nat.div_pos (Nat.le_of_dvd hm hd) (by norm_num)
  have hquot' : m / 7 < q := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hsmall
  have h7 : P 7 = 7 := by decide +kernel
  refine ⟨Nat.le_maxPrimeFac hm.ne' (by norm_num) hd, ?_⟩
  have he := Nat.maxPrimeFac_mul hquot.ne' (by norm_num : (7 : ℕ) ≠ 0)
  rw [Nat.div_mul_cancel hd] at he
  change P m = max (P (m / 7)) (P 7) at he
  rw [he, h7]
  exact max_lt (Nat.maxPrimeFac_le.trans_lt hquot') hq

lemma six_primeFactors {q : ℕ} (hq : q.Prime) :
    (6 * q).primeFactors = {2, 3, q} := by
  have h6 : (6 : ℕ).primeFactors = {2, 3} := by decide +kernel
  rw [Nat.primeFactors_mul (by norm_num) hq.ne_zero, h6, hq.primeFactors]
  ext p
  simp [or_comm, or_left_comm]

lemma rightLocal_family {q : ℕ} (hq : q.Prime) (hq7 : 7 < q)
    (hmod : q ≡ 6 [MOD 7]) : rightLocal (6 * q - 1) = 1 := by
  have hm : q % 7 = 6 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  have hd : 7 ∣ 6 * q - 1 := by
    refine ⟨6 * (q / 7) + 5, ?_⟩
    have hh := Nat.mod_add_div q 7
    rw [hm] at hh
    omega
  have hh := height_bounds_of_seven_dvd (m := 6 * q - 1) (q := q)
    (by omega) hq7 (by omega) hd
  have hsub : 6 * q - 1 + 1 = 6 * q := by omega
  have h2 : 2 ∣ 6 * q := dvd_mul_of_dvd_left (by norm_num) q
  have h3 : 3 ∣ 6 * q := dvd_mul_of_dvd_left (by norm_num) q
  have hqdiv : q ∣ 6 * q := dvd_mul_left q 6
  have hd2 : (6 * q) / 2 = 3 * q := by omega
  have hd3 : (6 * q) / 3 = 2 * q := by omega
  have hdq : (6 * q) / q = 6 := Nat.mul_div_cancel 6 hq.pos
  have hp2 : P (2 * q) = q := height_of_small_mul (by norm_num) (by omega) hq
  have hp3 : P (3 * q) = q := height_of_small_mul (by norm_num) (by omega) hq
  have hp6 : P 6 = 3 := by decide +kernel
  have hnlt : ¬P (6 * q - 1) < 3 := by omega
  have h2q : 2 ≠ q := by omega
  have h3q : 3 ≠ q := by omega
  simp [rightLocal, rightDeleted, hsub, six_primeFactors hq, h2q, h3q,
    h2, h3, hqdiv, hd2, hd3, hdq, hp2, hp3, hp6,
    Erdos371PrimeDeletion.compare, hh.2, hnlt]

lemma leftLocal_family {q : ℕ} (hq : q.Prime) (hq7 : 7 < q)
    (hmod : q ≡ 1 [MOD 7]) : leftLocal (6 * q) = -1 := by
  have hm : q % 7 = 1 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  have hd : 7 ∣ 6 * q + 1 := by
    refine ⟨6 * (q / 7) + 1, ?_⟩
    have hh := Nat.mod_add_div q 7
    rw [hm] at hh
    omega
  have hh := height_bounds_of_seven_dvd (m := 6 * q + 1) (q := q)
    (by omega) hq7 (by omega) hd
  have hd2 : (6 * q) / 2 = 3 * q := by omega
  have hd3 : (6 * q) / 3 = 2 * q := by omega
  have hdq : (6 * q) / q = 6 := Nat.mul_div_cancel 6 hq.pos
  have hp2 : P (2 * q) = q := height_of_small_mul (by norm_num) (by omega) hq
  have hp3 : P (3 * q) = q := height_of_small_mul (by norm_num) (by omega) hq
  have hp6 : P 6 = 3 := by decide +kernel
  have hnlt : ¬q < P (6 * q + 1) := by omega
  have h3lt : 3 < P (6 * q + 1) := by omega
  have h2q : 2 ≠ q := by omega
  have h3q : 3 ≠ q := by omega
  simp [leftLocal, six_primeFactors hq, h2q, h3q, hd2, hd3, hdq,
    hp2, hp3, hp6, Erdos371PrimeDeletion.compare, hnlt, h3lt]

/-- The right-deleted average is not pointwise nonpositive, even after
arbitrarily many initial inputs have been discarded. -/
theorem infinitely_many_right_positive : {n | 0 < rightLocal n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨q, hqN, hq, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max N 7)
    (q := 7) (a := 6) (by norm_num) (by norm_num)
  refine ⟨6 * q - 1, ?_, ?_⟩
  · change 0 < rightLocal (6 * q - 1)
    rw [rightLocal_family hq (by omega) hmod]
    norm_num
  · omega

/-- Likewise, the left-deleted average is not pointwise nonnegative. -/
theorem infinitely_many_left_negative : {n | leftLocal n < 0}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨q, hqN, hq, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max N 7)
    (q := 7) (a := 1) (by norm_num) (by norm_num)
  refine ⟨6 * q, ?_, ?_⟩
  · change leftLocal (6 * q) < 0
    rw [leftLocal_family hq (by omega) hmod]
    norm_num
  · omega

end Erdos371PrimeDeletionLocal

#print axioms Erdos371PrimeDeletionLocal.rightLocal_family
#print axioms Erdos371PrimeDeletionLocal.leftLocal_family
#print axioms Erdos371PrimeDeletionLocal.infinitely_many_right_positive
#print axioms Erdos371PrimeDeletionLocal.infinitely_many_left_negative
