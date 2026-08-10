import FormalConjectures.Util.ProblemImports

def N : Nat := 201886 * 3 ^ 39101 - 1
def inv5 : Nat := (2*N + 1) / 5

theorem N_pos : 0 < N := by
  unfold N
  apply Nat.sub_pos_of_lt
  have hpow : 0 < 3 ^ 39101 := pow_pos (by norm_num) _
  have hle : 201886 ≤ 201886 * 3 ^ 39101 := Nat.le_mul_of_pos_right 201886 hpow
  exact lt_of_lt_of_le (by norm_num : 1 < 201886) hle


lemma pow3_mod5 : 3 ^ 39101 ≡ 3 [MOD 5] := by
  rw [show 39101 = 4 * 9775 + 1 by norm_num]
  rw [pow_add, pow_mul]
  have h : 3 ^ 4 ≡ 1 [MOD 5] := by norm_num [Nat.ModEq]
  have hpow := Nat.ModEq.pow 9775 h
  have h3 : 3 ≡ 3 [MOD 5] := Nat.ModEq.refl 3
  have hmul := Nat.ModEq.mul hpow h3
  simpa using hmul

lemma N_mod5 : N ≡ 2 [MOD 5] := by
  unfold N
  have h201886 : 201886 ≡ 1 [MOD 5] := by norm_num [Nat.ModEq]
  have hmul := Nat.ModEq.mul h201886 pow3_mod5
  have hA : 201886 * 3 ^ 39101 ≡ 3 [MOD 5] := by simpa using hmul
  have hsub := Nat.ModEq.sub (by
    have hpow : 0 < 3 ^ 39101 := pow_pos (by norm_num) _
    exact Nat.succ_le_of_lt (Nat.mul_pos (by norm_num : 0 < 201886) hpow)) (by norm_num : 1 ≤ 3) hA (Nat.ModEq.refl 1)
  simpa using hsub

lemma dvd2N1 : 5 ∣ 2 * N + 1 := by
  have h2 := Nat.ModEq.mul_left 2 N_mod5
  have h := Nat.ModEq.add h2 (Nat.ModEq.refl 1)
  have h0 : 2 * N + 1 ≡ 0 [MOD 5] := by
    simpa [Nat.ModEq] using h
  rw [Nat.dvd_iff_mod_eq_zero]
  exact h0

theorem inv5_spec : 5 * inv5 = 2 * N + 1 := by
  unfold inv5
  exact Nat.mul_div_cancel' dvd2N1
