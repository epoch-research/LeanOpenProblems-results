import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option exponentiation.threshold 300

lemma pow_period_odd : 2^29400 ≡ 1 [MOD 137543] := by
  have h343 : 2^147 ≡ 1 [MOD 343] := by norm_num [Nat.ModEq]
  have h401 : 2^200 ≡ 1 [MOD 401] := by norm_num [Nat.ModEq]
  have h343D : 2^29400 ≡ 1 [MOD 343] := by
    have h := h343.pow 200
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have h401D : 2^29400 ≡ 1 [MOD 401] := by
    have h := h401.pow 147
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hc : Nat.Coprime 343 401 := by norm_num
  have := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h343D, h401D⟩
  norm_num at this ⊢
  exact this

lemma pow_two_mod4_zero {e : Nat} (he : 2 ≤ e) : 2^e ≡ 0 [MOD 4] := by
  rw [Nat.modEq_zero_iff_dvd]
  use 2^(e-2)
  have h : e = 2 + (e - 2) := by omega
  rw [h, pow_add]
  norm_num

lemma pow_period_modEq (a t : Nat) (ha : 2 ≤ a) : 2^(a + t * 29400) ≡ 2^a [MOD 550172] := by
  have hO0 : (2^29400)^t ≡ 1^t [MOD 137543] := (pow_period_odd.pow t)
  have hO : 2^(a + t * 29400) ≡ 2^a [MOD 137543] := by
    calc
      2^(a + t * 29400) = 2^a * (2^29400)^t := by
        have heq : 2^(t * 29400) = (2^29400)^t := by
          rw [mul_comm t 29400, pow_mul]
        rw [pow_add, heq]
      _ ≡ 2^a * 1^t [MOD 137543] := hO0.mul_left (2^a)
      _ = 2^a := by simp
  have h4 : 2^(a + t * 29400) ≡ 2^a [MOD 4] := by
    exact (pow_two_mod4_zero (by omega : 2 ≤ a + t * 29400)).trans (pow_two_mod4_zero ha).symm
  have h := Nat.mod_lcm h4 hO
  have hlcm : Nat.lcm 4 137543 = 550172 := by norm_num [Nat.lcm, Nat.gcd]
  simpa [hlcm] using h

