import FormalConjectures.Util.ProblemImports

example : ((2^171 + 1) / 9) % 18 = 3 := by
  norm_num

example : (2 ^ ((2^171 + 1) / 9)) % 19 = 8 := by
  have hE : ((2^171 + 1) / 9) % 18 = 3 := by norm_num
  -- try omega/simp?
  omega

example : ¬ (171 ∣ 2 ^ ((2^171 + 1) / 9) + 1) := by
  intro h
  have h19 : 19 ∣ 2 ^ ((2^171 + 1) / 9) + 1 := dvd_trans (by norm_num : 19 ∣ 171) h
  have hm : (2 ^ ((2^171 + 1) / 9) + 1) % 19 = 9 := by
    have hpow : (2 ^ ((2^171 + 1) / 9)) % 19 = 8 := by
      have hE : ((2^171 + 1) / 9) % 18 = 3 := by norm_num
      omega
    omega
  have hz : (2 ^ ((2^171 + 1) / 9) + 1) % 19 = 0 := Nat.dvd_iff_mod_eq_zero.mp h19
  omega
