import Submission.Work

/-! An infinite exponent-family obstruction. This does not settle Erdős 406. -/

namespace Erdos406Work

lemma two_pow_three_pow_first_order (s : ℕ) :
    ∃ q : ℤ, (2 : ℤ) ^ (3 ^ s) = -1 + 3 ^ (s + 1) + 3 ^ (s + 2) * q := by
  induction s with
  | zero => exact ⟨0, by norm_num⟩
  | succ s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q - 3 ^ s * (1 + 3 * q) ^ 2 + (3 ^ s) ^ 2 * (1 + 3 * q) ^ 3, ?_⟩
    rw [Nat.pow_succ, pow_mul, hq]
    simp only [pow_succ]
    ring

lemma two_pow_odd_scaled_first_order (s u : ℕ) (hu : Odd u) :
    Int.ModEq (3 ^ (s + 2)) ((2 : ℤ) ^ (3 ^ s * u))
      (-1 + (u : ℤ) * 3 ^ (s + 1)) := by
  obtain ⟨q, hq⟩ := two_pow_three_pow_first_order s
  have hbase : Int.ModEq (3 ^ (s + 2)) ((2 : ℤ) ^ (3 ^ s))
      (-1 + 3 ^ (s + 1)) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-q, ?_⟩
    rw [hq]
    ring
  have hpow := hbase.pow u
  rw [← pow_mul] at hpow
  apply hpow.trans
  have hu' : Even (u - 1) := by
    obtain ⟨t, ht⟩ := hu
    exact ⟨t, by omega⟩
  have hlin := sq_dvd_add_pow_sub_sub (3 ^ (s + 1) : ℤ) (-1) u
  rw [hu.neg_one_pow, hu'.neg_one_pow, one_mul] at hlin
  have hd : (3 : ℤ) ^ (s + 2) ∣ (3 ^ (s + 1)) ^ 2 := by
    rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)
  apply Int.modEq_iff_dvd.mpr
  convert (dvd_trans hd hlin).neg_right using 1
  ring

lemma forbidden_exponent_unit_residue (s t : ℕ) :
    2 ^ (3 ^ s * (6 * t + 5) - 1) % 3 ^ (s + 2) =
      ternaryRepunit (s + 1) + 2 * 3 ^ (s + 1) := by
  let k := 3 ^ s * (6 * t + 5) - 1
  have hk : k + 1 = 3 ^ s * (6 * t + 5) := by
    dsimp [k]
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (by positivity))
  have hu : Odd (6 * t + 5) := ⟨3 * t + 2, by omega⟩
  have hm := two_pow_odd_scaled_first_order s (6 * t + 5) hu
  rw [← hk, show (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 from pow_succ _ _] at hm
  have hsmall : Int.ModEq (3 ^ (s + 2))
      (-1 + ((6 * t + 5 : ℕ) : ℤ) * 3 ^ (s + 1))
      (-1 + 5 * 3 ^ (s + 1)) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-2 * (t : ℤ), ?_⟩
    push_cast
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    ring
  have hm' := hm.trans hsmall
  let R := ternaryRepunit (s + 1) + 2 * 3 ^ (s + 1)
  have hR : 2 * R = -1 + (5 : ℤ) * 3 ^ (s + 1) := by
    have hh := ternaryRepunit_identity (s + 1)
    have hi : 2 * (R : ℤ) + 1 = 5 * 3 ^ (s + 1) := by
      dsimp [R]
      exact_mod_cast (by omega : 2 * (ternaryRepunit (s + 1) + 2 * 3 ^ (s + 1)) + 1 =
        5 * 3 ^ (s + 1))
    omega
  have hmNat : Nat.ModEq (3 ^ (s + 2)) (2 * 2 ^ k) (2 * R) := by
    apply Int.natCast_modEq_iff.mp
    push_cast
    rw [hR]
    simpa [mul_comm] using hm'
  have hc : Nat.Coprime 2 (3 ^ (s + 2)) := (by decide : Nat.Coprime 2 3).pow_right _
  have hn := hmNat.cancel_left_of_coprime hc.symm
  have hRlt : R < 3 ^ (s + 2) := by
    have hh := ternaryRepunit_identity (s + 1)
    dsimp [R]
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    omega
  have hres : 2 ^ k % 3 ^ (s + 2) = R := by
    change 2 ^ k % 3 ^ (s + 2) = R % 3 ^ (s + 2) at hn
    rwa [Nat.mod_eq_of_lt hRlt] at hn
  exact hres

lemma forbidden_exponent_unit_family (s t : ℕ) :
    ¬ Nat.digits 3 (2 ^ (3 ^ s * (6 * t + 5) - 1)) ⊆ [0, 1] := by
  intro hg
  have hbad := (digits_iff_no_carries _).mp hg (s + 2)
  rw [forbidden_exponent_unit_residue] at hbad
  have hh := ternaryRepunit_identity (s + 1)
  rw [show s + 2 = (s + 1) + 1 by omega, pow_succ] at hbad
  have hp : 0 < 3 ^ (s + 1) := by positivity
  omega

/-- Every good exponent `k` has 3-free part of `k+1` congruent to one modulo six.
This condition still allows infinitely many exponents. -/
lemma good_exponent_plus_one_unit {k : ℕ}
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) :
    ∃ s t : ℕ, k + 1 = 3 ^ s * (6 * t + 1) := by
  obtain ⟨s, u, hnu, hku⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (by omega : k + 1 ≠ 0) 3 (by decide)
  have hodd : Odd u := by
    have ho : Odd (3 ^ s * u) := by
      rw [← hku]
      exact Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr (even_exponent hg))
    exact (Nat.odd_mul.mp ho).2
  have hmod2 := Nat.odd_iff.mp hodd
  have hmod3 : u % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hnu
  have hcases : u % 6 = 1 ∨ u % 6 = 5 := by omega
  rcases hcases with h1 | h5
  · refine ⟨s, u / 6, ?_⟩
    have he : u = 6 * (u / 6) + 1 := by omega
    simpa only [← he] using hku
  · have he : u = 6 * (u / 6) + 5 := by omega
    have hk : k = 3 ^ s * (6 * (u / 6) + 5) - 1 := by rw [← he, ← hku]; omega
    rw [hk] at hg
    exact (forbidden_exponent_unit_family s (u / 6) hg).elim

lemma forbidden_initial_ones_then_two_value (s t : ℕ) :
    ¬ Nat.digits 3 (4 ^ (ternaryRepunit s + 3 ^ s * (3 * t + 2))) ⊆ [0, 1] := by
  have hi := ternaryRepunit_identity s
  have he : 2 * (ternaryRepunit s + 3 ^ s * (3 * t + 2)) =
      3 ^ s * (6 * t + 5) - 1 := by
    have he' : 2 * (ternaryRepunit s + 3 ^ s * (3 * t + 2)) + 1 =
        3 ^ s * (6 * t + 5) := by nlinarith
    omega
  have hp : 4 ^ (ternaryRepunit s + 3 ^ s * (3 * t + 2)) =
      2 ^ (3 ^ s * (6 * t + 5) - 1) := by
    rw [← he, pow_mul]
    norm_num
  rw [hp]
  exact forbidden_exponent_unit_family s t

/-- In the least-significant-first convention, a run of ones followed by a two
in the exponent forces a two in the digits of the corresponding power of four.
The tail word is arbitrary. -/
lemma forbidden_initial_ones_then_two (s : ℕ) (w : List ℕ) :
    ¬ Nat.digits 3 (4 ^ Nat.ofDigits 3 (List.replicate s 1 ++ 2 :: w)) ⊆ [0, 1] := by
  have he : Nat.ofDigits 3 (List.replicate s 1 ++ 2 :: w) =
      ternaryRepunit s + 3 ^ s * (3 * Nat.ofDigits 3 w + 2) := by
    simp [ternaryRepunit, Nat.ofDigits_append, Nat.ofDigits_cons, add_comm]
  rw [he]
  exact forbidden_initial_ones_then_two_value s (Nat.ofDigits 3 w)

#print axioms forbidden_exponent_unit_family
#print axioms good_exponent_plus_one_unit
#print axioms forbidden_initial_ones_then_two
end Erdos406Work
