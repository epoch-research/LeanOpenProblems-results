import Submission.ThirteenSixteenthPowerBound
open Erdos970 Erdos970.FiniteSelberg
set_option maxRecDepth 10000
noncomputable def Th : ℕ := max (384 * (thirteenSixteenthCutoffScale + 1))
    (twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16)
lemma generic_envelope_le (A k t : ℕ) (hA : A ^ 16 ≤ k) (hkt : k ≤ t ^ 16) : A ≤ t :=
  (Nat.pow_le_pow_iff_left (by decide : 16 ≠ 0)).mp (hA.trans hkt)
example (k t : ℕ) (hk : Th ^ 16 ≤ k) (hkt : k ≤ t ^ 16) : Th ≤ t :=
  generic_envelope_le Th k t hk hkt
#print axioms generic_envelope_le
lemma Th_pos : 0 < Th := by
  unfold Th
  have hh := le_max_left (384 * (thirteenSixteenthCutoffScale + 1))
    (twentyOneEighthConstant * 2 ^ 21 * 65536 ^ 16)
  omega
example (k : ℕ) (hk : Th ^ 16 ≤ k) : 0 < k := (Nat.pow_pos Th_pos).trans_le hk
lemma generic_envelope_pos (A k : ℕ) (hA : 0 < A) (hk : A ^ 16 ≤ k) : 0 < k :=
  (Nat.pow_pos hA).trans_le hk
example (k : ℕ) (hk : Th ^ 16 ≤ k) : 0 < k := generic_envelope_pos Th k Th_pos hk
