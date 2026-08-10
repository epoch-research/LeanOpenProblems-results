import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1000

lemma pow_mod49_mod588 (a : Nat) : 2^a ≡ 2^(a % 588) [MOD 49] := by
  have hper : 2^588 ≡ 1 [MOD 49] := by norm_num [Nat.ModEq]
  have hdecomp : a = a % 588 + (a / 588) * 588 := by
    rw [mul_comm, Nat.mod_add_div]
  nth_rewrite 1 [hdecomp]
  rw [pow_add]
  have hp : 2^((a / 588) * 588) = (2^588)^(a/588) := by rw [mul_comm, pow_mul]
  rw [hp]
  have hpow := hper.pow (a/588)
  simpa using hpow.mul_left (2^(a%588))

lemma possible_mod (a : Nat) (h4 : a % 4 = 3) (h49 : 2^a ≡ a + 13573 [MOD 49]) :
    a % 588 = 183 ∨ a % 588 = 415 ∨ a % 588 = 431 := by
  have hpow := pow_mod49_mod588 a
  have ha49 : a ≡ a % 588 [MOD 49] := ((Nat.mod_modEq a 588).of_dvd (by norm_num : 49 ∣ 588)).symm
  have hsmall49 : 2^(a%588) ≡ (a%588) + 13573 [MOD 49] := by
    exact hpow.symm.trans (h49.trans (ha49.add Nat.ModEq.rfl))
  have hsmall4 : (a%588) % 4 = 3 := by
    rw [← h4]
    exact Nat.mod_mod_of_dvd a (by norm_num : 4 ∣ 588)
  let s := a % 588
  have hslt : s < 588 := Nat.mod_lt _ (by norm_num)
  change s % 4 = 3 at hsmall4
  change 2^s ≡ s + 13573 [MOD 49] at hsmall49
  change s = 183 ∨ s = 415 ∨ s = 431
  interval_cases s
  all_goals
    norm_num at hsmall4
    try contradiction
    try norm_num [Nat.ModEq] at hsmall49
    try simp
