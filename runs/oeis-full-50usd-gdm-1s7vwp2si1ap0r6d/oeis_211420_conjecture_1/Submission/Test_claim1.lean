import FormalConjectures.Util.ProblemImports

open Nat

lemma p_pow_gt_of_gt_padicValNat_factorial {p X : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : k = padicValNat p X.factorial) {i : ℕ} (hi : i > k) : p ^ i > X := by
  by_contra h_le
  push_neg at h_le
  have h_pos : p ^ i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i hp.out.ne_zero)
  have h_dvd := Nat.dvd_factorial h_pos h_le
  have h_ne : X.factorial ≠ 0 := Nat.factorial_ne_zero X
  rw [padicValNat_dvd_iff_le h_ne] at h_dvd
  rw [← hk] at h_dvd
  omega
