import FormalConjectures.Util.ProblemImports

lemma two_pow_mod19_of_mod18_eq_3 (n : ℕ) (h : n % 18 = 3) : (2 ^ n) % 19 = 8 := by
  have hn : n = 18 * (n / 18) + 3 := by
    rw [← h]
    exact (Nat.div_add_mod n 18).symm
  rw [hn, pow_add, pow_mul]
  have hbase : (2 ^ 18) ≡ 1 [MOD 19] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 18) ^ (n / 18) ≡ 1 ^ (n / 18) [MOD 19] := hbase.pow _
  have hmul : (2 ^ 18) ^ (n / 18) * 2 ^ 3 ≡ 1 ^ (n / 18) * 8 [MOD 19] := by
    exact hpow.mul (by norm_num [Nat.ModEq])
  simpa [Nat.ModEq] using hmul

example : ¬ (171 ∣ 2 ^ ((2^171 + 1) / 9) + 1) := by
  intro h
  have h19 : 19 ∣ 2 ^ ((2^171 + 1) / 9) + 1 := dvd_trans (by norm_num : 19 ∣ 171) h
  have hzero : 2 ^ ((2^171 + 1) / 9) + 1 ≡ 0 [MOD 19] := Nat.modEq_zero_iff_dvd.mpr h19
  have hpoweq : (2 ^ ((2^171 + 1) / 9)) % 19 = 8 := by
    apply two_pow_mod19_of_mod18_eq_3
    norm_num
  have hpowmod : 2 ^ ((2^171 + 1) / 9) ≡ 8 [MOD 19] := hpoweq
  have hsum : 2 ^ ((2^171 + 1) / 9) + 1 ≡ 9 [MOD 19] := by
    simpa using hpowmod.add (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD 19])
  have hbad : 9 ≡ 0 [MOD 19] := hsum.symm.trans hzero
  norm_num [Nat.ModEq] at hbad
