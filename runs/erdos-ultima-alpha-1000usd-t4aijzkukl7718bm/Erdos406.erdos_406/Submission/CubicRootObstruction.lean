import Submission.GeneralResidueObstruction

/-! Counterexamples to unrestricted plain-cube descent. These numbers have an
odd divisor, so they do not disprove the pure-power missing-digit conjecture. -/

namespace Erdos406Work

lemma plain_cube_descent_counterexample :
    Nat.digits 3 (562 ^ 3) ⊆ [0, 1] ∧ ¬ Nat.digits 3 562 ⊆ [0, 1] ∧
      (562 : ℕ) = 2 * 281 := by
  decide +kernel

lemma good_cube_mul_separated {n r : ℕ}
    (hg : Nat.digits 3 (n ^ 3) ⊆ [0, 1])
    (hr : (Nat.digits 3 (n ^ 3)).length ≤ r) :
    Nat.digits 3 ((n * (3 ^ (r + 1) + 1)) ^ 3) ⊆ [0, 1] := by
  have hnlt : n ^ 3 < 3 ^ r :=
    (Nat.lt_base_pow_length_digits (b := 3) (m := n ^ 3) (by decide)).trans_le
      (Nat.pow_le_pow_right (by decide) hr)
  have hnlt1 : n ^ 3 < 3 ^ (r + 1) :=
    hnlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hnlt2 : n ^ 3 < 3 ^ (r + 2) :=
    hnlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hg1 := good_add_shifted hnlt hg hg
  have hg2 := good_add_shifted hnlt1 hg hg1
  have hg3 := good_add_shifted hnlt2 hg hg2
  have he : (n * (3 ^ (r + 1) + 1)) ^ 3 =
      n ^ 3 + 3 ^ (r + 2) * (n ^ 3 + 3 ^ (r + 1) * (n ^ 3 + 3 ^ r * n ^ 3)) := by
    simp only [pow_succ]
    ring
  rw [he]
  exact hg3

lemma bad_mul_separated {n L : ℕ} (hn : 0 < n)
    (hbad : ¬ Nat.digits 3 n ⊆ [0, 1]) (hL : (Nat.digits 3 n).length ≤ L) :
    ¬ Nat.digits 3 (n * (3 ^ L + 1)) ⊆ [0, 1] := by
  have he := Nat.digits_append_zeroes_append_digits (b := 3) (n := n) (m := n)
    (k := L - (Nat.digits 3 n).length) (by decide) hn
  rw [Nat.add_sub_of_le hL] at he
  have hv : n * (3 ^ L + 1) = n + 3 ^ L * n := by ring
  rw [hv, ← he]
  intro hg
  apply hbad
  intro d hd
  exact hg (by simp [hd])

/-- The cubic counterexample can be amplified past any bound while gaining a
factor of four and retaining the original root as a divisor. -/
lemma amplify_bad_cube_root (n B : ℕ) (hn : 0 < n)
    (hg : Nat.digits 3 (n ^ 3) ⊆ [0, 1]) (hbad : ¬ Nat.digits 3 n ⊆ [0, 1]) :
    ∃ m : ℕ, B < m ∧ Nat.digits 3 (m ^ 3) ⊆ [0, 1] ∧
      ¬ Nat.digits 3 m ⊆ [0, 1] ∧ 4 * n ∣ m ∧ Nat.ModEq 3 m n := by
  let r := 2 * ((Nat.digits 3 (n ^ 3)).length + (Nat.digits 3 n).length + B + 1)
  have hrc : (Nat.digits 3 (n ^ 3)).length ≤ r := by dsimp [r]; omega
  have hrn : (Nat.digits 3 n).length ≤ r + 1 := by dsimp [r]; omega
  have hrB : B < r + 1 := by dsimp [r]; omega
  have hodd : Odd (r + 1) := ⟨r / 2, by dsimp [r]; omega⟩
  have hf := four_dvd_three_pow_odd_add_one hodd
  let m := n * (3 ^ (r + 1) + 1)
  have hnM : B < m := by
    have hp : r + 1 < 3 ^ (r + 1) := Nat.lt_pow_self (by decide)
    have hh : 3 ^ (r + 1) + 1 ≤ m := Nat.le_mul_of_pos_left _ hn
    omega
  refine ⟨m, hnM, good_cube_mul_separated hg hrc, bad_mul_separated hn hbad hrn, ?_, ?_⟩
  · simpa only [mul_comm 4 n] using Nat.mul_dvd_mul_left n hf
  · dsimp [m]
    have hp : Nat.ModEq 3 (3 ^ (r + 1) + 1) 1 := by
      simp [Nat.ModEq, pow_succ, Nat.add_mod]
    simpa only [mul_one] using hp.mul_left n

/-- Even arbitrarily strong powers-of-four divisibility do not repair plain
cubic descent. The retained odd factor281 keeps these from being powers of2. -/
lemma arbitrary_guard_bad_cube_root (K B : ℕ) :
    ∃ n : ℕ, B < n ∧ 4 ^ K ∣ n ∧ n % 3 = 1 ∧
      Nat.digits 3 (n ^ 3) ⊆ [0, 1] ∧ ¬ Nat.digits 3 n ⊆ [0, 1] ∧
      281 ∣ n ∧ ¬ n.isPowerOfTwo := by
  have hbasegood := plain_cube_descent_counterexample.1
  have hbasebad := plain_cube_descent_counterexample.2.1
  have hexists : ∀ k : ℕ, ∃ n : ℕ, 0 < n ∧ 4 ^ k ∣ n ∧ n % 3 = 1 ∧
      Nat.digits 3 (n ^ 3) ⊆ [0, 1] ∧ ¬ Nat.digits 3 n ⊆ [0, 1] ∧ 281 ∣ n := by
    intro k
    induction k with
    | zero => exact ⟨562, by decide, by simp, by decide, hbasegood, hbasebad, by decide⟩
    | succ k ih =>
      obtain ⟨n, hn, hnk, hn3, hg, hbad, h281⟩ := ih
      obtain ⟨m, hm, hgm, hbadm, hdiv, hmod⟩ := amplify_bad_cube_root n 0 hn hg hbad
      have hnm : n ∣ m := dvd_trans (dvd_mul_left n 4) hdiv
      have hkm : 4 ^ (k + 1) ∣ m := by
        apply dvd_trans _ hdiv
        simpa only [pow_succ'] using Nat.mul_dvd_mul_left 4 hnk
      exact ⟨m, hm, hkm, Eq.trans hmod hn3, hgm, hbadm, dvd_trans h281 hnm⟩
  obtain ⟨n, hn, hnk, hn3, hg, hbad, h281⟩ := hexists K
  obtain ⟨m, hmB, hgm, hbadm, hdiv, hmod⟩ := amplify_bad_cube_root n B hn hg hbad
  have hnm : n ∣ m := dvd_trans (dvd_mul_left n 4) hdiv
  have hm281 : 281 ∣ m := dvd_trans h281 hnm
  refine ⟨m, hmB, dvd_trans hnk hnm, Eq.trans hmod hn3, hgm, hbadm, hm281, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk] at hm281
  have hprime : Nat.Prime 281 := by norm_num
  have h2 := hprime.dvd_of_dvd_pow hm281
  norm_num at h2

#print axioms plain_cube_descent_counterexample
#print axioms arbitrary_guard_bad_cube_root
end Erdos406Work
