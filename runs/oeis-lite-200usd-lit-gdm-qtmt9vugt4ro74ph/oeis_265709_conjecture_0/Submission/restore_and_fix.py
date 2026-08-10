import shutil

src = "/workspace/leanproject/Submission/Spec.lean.before_delete"
dest = "/workspace/leanproject/Submission/Spec.lean"
shutil.copy(src, dest)

with open(dest, "r") as f:
    content = f.read()

# 1. Replace from padicValRat_add_of_val_zero to padicValRat_two_sum_divisors_pow_two_odd
start_marker = "lemma padicValRat_add_of_val_zero"
end_marker = "lemma padicValRat_two_sum_divisors_pow_two_odd"

start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx == -1 or end_idx == -1:
    print("Error: Fix markers not found!")
    exit(1)

new_lemmas = """lemma padicValRat_add_of_val_zero (A B : ℚ) (hAnz : A ≠ 0) (hBnz : B ≠ 0) (hA : padicValRat 2 A = 0) (hB : padicValRat 2 B = 0) (hAB : A + B ≠ 0) :
  1 ≤ padicValRat 2 (A + B) := by
  have h_denA : padicValNat 2 A.den = 0 := den_odd_of_val_nonneg A (by linarith)
  have h_denB : padicValNat 2 B.den = 0 := den_odd_of_val_nonneg B (by linarith)
  have h_numA : padicValInt 2 A.num = 0 := by
    have h_val := hA
    rw [padicValRat_def, h_denA] at h_val
    omega
  have h_numB : padicValInt 2 B.num = 0 := by
    have h_val := hB
    rw [padicValRat_def, h_denB] at h_val
    omega
  have h_nz_A_num : A.num ≠ 0 := Rat.num_ne_zero.mpr hAnz
  have h_nz_B_num : B.num ≠ 0 := Rat.num_ne_zero.mpr hBnz
  have hA_odd : ¬ 2 ∣ A.num := by
    intro hd
    have : 1 ≤ padicValInt 2 A.num := by
      have hd'' : (2 : ℤ) ^ 1 ∣ A.num := by exact_mod_cast hd
      have h_or := (@padicValInt_dvd_iff 2 ⟨Nat.prime_two⟩ 1 A.num).mp hd''
      rcases h_or with h_zero | h_le
      · contradiction
      · exact h_le
    omega
  have hB_odd : ¬ 2 ∣ B.num := by
    intro hd
    have : 1 ≤ padicValInt 2 B.num := by
      have hd'' : (2 : ℤ) ^ 1 ∣ B.num := by exact_mod_cast hd
      have h_or := (@padicValInt_dvd_iff 2 ⟨Nat.prime_two⟩ 1 B.num).mp hd''
      rcases h_or with h_zero | h_le
      · contradiction
      · exact h_le
    omega
  have hAd_odd : ¬ 2 ∣ (A.den : ℤ) := by
    intro hd
    have hd_nat : 2 ∣ A.den := by exact_mod_cast hd
    have : 1 ≤ padicValNat 2 A.den := one_le_padicValNat_of_dvd (by positivity) hd_nat
    omega
  have hBd_odd : ¬ 2 ∣ (B.den : ℤ) := by
    intro hd
    have hd_nat : 2 ∣ B.den := by exact_mod_cast hd
    have : 1 ≤ padicValNat 2 B.den := one_le_padicValNat_of_dvd (by positivity) hd_nat
    omega
  obtain ⟨qA, hqA⟩ : ∃ q, A.num = 2 * q + 1 := by
    rcases Int.emod_two_eq_zero_or_one A.num with h | h
    · have : 2 ∣ A.num := Int.dvd_of_emod_eq_zero h
      contradiction
    · use A.num / 2; omega
  obtain ⟨qB, hqB⟩ : ∃ q, B.num = 2 * q + 1 := by
    rcases Int.emod_two_eq_zero_or_one B.num with h | h
    · have : 2 ∣ B.num := Int.dvd_of_emod_eq_zero h
      contradiction
    · use B.num / 2; omega
  obtain ⟨qAd, hqAd⟩ : ∃ q, (A.den : ℤ) = 2 * q + 1 := by
    rcases Int.emod_two_eq_zero_or_one (A.den : ℤ) with h | h
    · have : 2 ∣ (A.den : ℤ) := Int.dvd_of_emod_eq_zero h
      contradiction
    · use (A.den : ℤ) / 2; omega
  obtain ⟨qBd, hqBd⟩ : ∃ q, (B.den : ℤ) = 2 * q + 1 := by
    rcases Int.emod_two_eq_zero_or_one (B.den : ℤ) with h | h
    · have : 2 ∣ (B.den : ℤ) := Int.dvd_of_emod_eq_zero h
      contradiction
    · use (B.den : ℤ) / 2; omega
  have h_dvd : (2 : ℤ) ∣ (A.num * (B.den : ℤ) + B.num * (A.den : ℤ)) := by
    use qA * (2 * qBd + 1) + qB * (2 * qAd + 1) + qAd + qBd + 1
    rw [hqA, hqB, hqAd, hqBd]
    ring
  rw [padicValRat_def]
  have h_eq_div : ((A + B).num : ℚ) / ((A + B).den : ℚ) = (A.num : ℚ) / (A.den : ℚ) + (B.num : ℚ) / (B.den : ℚ) := by
    rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  have h_cast : (((A + B).num * (A.den : ℤ) * (B.den : ℤ) : ℤ) : ℚ) = (((A + B).den * (A.num * (B.den : ℤ) + B.num * (A.den : ℤ)) : ℤ) : ℚ) := by
    push_cast
    have h_denA_nz : (A.den : ℚ) ≠ 0 := by positivity
    have h_denB_nz : (B.den : ℚ) ≠ 0 := by positivity
    have h_denAB_nz : ((A + B).den : ℚ) ≠ 0 := by positivity
    have h_mul_eq : (((A + B).num : ℚ) / ((A + B).den : ℚ)) * ((A + B).den : ℚ) * (A.den : ℚ) * (B.den : ℚ) =
      ((A.num : ℚ) / (A.den : ℚ) + (B.num : ℚ) / (B.den : ℚ)) * ((A + B).den : ℚ) * (A.den : ℚ) * (B.den : ℚ) := by
      rw [h_eq_div]
    rw [div_mul_cancel₀ _ h_denAB_nz] at h_mul_eq
    have h_final : ((A.num : ℚ) / (A.den : ℚ) + (B.num : ℚ) / (B.den : ℚ)) * ((A + B).den : ℚ) * (A.den : ℚ) * (B.den : ℚ) =
      ((A + B).den : ℚ) * ((A.num : ℚ) * (B.den : ℚ) + (B.num : ℚ) * (A.den : ℚ)) := by
      field_simp; try ring
    rw [h_final] at h_mul_eq
    exact h_mul_eq
  have h_eq : (A + B).num * (A.den : ℤ) * (B.den : ℤ) = (A + B).den * (A.num * (B.den : ℤ) + B.num * (A.den : ℤ)) := by
    exact_mod_cast h_cast
  have h_val_eq : padicValInt 2 ((A + B).num * (A.den : ℤ) * (B.den : ℤ)) = padicValInt 2 ((A + B).den * (A.num * (B.den : ℤ) + B.num * (A.den : ℤ))) :=
    congr_arg (padicValInt 2) h_eq
  have h_nz_AB_num : (A + B).num ≠ 0 := Rat.num_ne_zero.mpr hAB
  have h_nz_Ad : (A.den : ℤ) ≠ 0 := by positivity
  have h_nz_Bd : (B.den : ℤ) ≠ 0 := by positivity
  have h_nz_denAB : ((A + B).den : ℤ) ≠ 0 := by positivity
  have h_nz_numAB_denA_denB : (A + B).num * (A.den : ℤ) * (B.den : ℤ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero h_nz_AB_num h_nz_Ad) h_nz_Bd
  have h_nz_sum : (A.num * (B.den : ℤ) + B.num * (A.den : ℤ)) ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at h_eq
    exact h_nz_numAB_denA_denB h_eq
  rw [padicValInt.mul (mul_ne_zero h_nz_AB_num h_nz_Ad) h_nz_Bd] at h_val_eq
  rw [padicValInt.mul h_nz_AB_num h_nz_Ad] at h_val_eq
  rw [padicValInt.mul h_nz_denAB h_nz_sum] at h_val_eq
  have h_val_Ad : padicValInt 2 (A.den : ℤ) = 0 := h_denA
  have h_val_Bd : padicValInt 2 (B.den : ℤ) = 0 := h_denB
  have h_val_denAB : padicValInt 2 ((A + B).den : ℤ) = padicValNat 2 (A + B).den := rfl
  rw [h_val_Ad, h_val_Bd, h_val_denAB] at h_val_eq
  simp only [add_zero] at h_val_eq
  have h_val_sum : padicValInt 2 (A.num * (B.den : ℤ) + B.num * (A.den : ℤ)) ≥ 1 := by
    have h_dvd'' : (2 : ℤ) ^ 1 ∣ (A.num * (B.den : ℤ) + B.num * (A.den : ℤ)) := by exact_mod_cast h_dvd
    have h_or := (@padicValInt_dvd_iff 2 ⟨Nat.prime_two⟩ 1 (A.num * (B.den : ℤ) + B.num * (A.den : ℤ))).mp h_dvd''
    rcases h_or with h_zero | h_le
    · contradiction
    · exact h_le
  omega

lemma sum_range_odd_split (k : ℕ) (F : ℕ → ℚ) :
  (∑ j ∈ range (2 * k + 2), F j) = F 0 + (∑ i ∈ range k, (F (2 * i + 1) + F (2 * i + 2))) + F (2 * k + 1) := by
  induction' k with k ih
  · rw [sum_range_succ, sum_range_succ]
    simp
  · have h_eq1 : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
    have h_eq2 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    rw [h_eq1, h_eq2]
    rw [sum_range_succ F (2 * k + 3)]
    rw [sum_range_succ F (2 * k + 2)]
    rw [sum_range_succ (fun i => F (2 * i + 1) + F (2 * i + 2)) k]
    rw [ih]
    ring

lemma sum_divisors_pow_two_odd_split (k : ℕ) :
  ((2^(2*k+1)).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) =
  ((2^(2*k)).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) +
  (1 : ℚ) / (↑(sigma 1 (2^(2*k+1))) : ℚ) := by
  rw [sum_divisors_pow_two (2*k+1)]
  rw [sum_divisors_pow_two (2*k)]
  have h_eq : 2 * k + 1 + 1 = 2 * k + 2 := by ring
  rw [h_eq]
  rw [sum_range_succ]
  rw [sigma_one_pow_two (2*k+1)]
  have h_ge : 1 ≤ 2^(2*k+1+1) := Nat.one_le_pow (2*k+1+1) 2 (by decide)
  rw [Nat.cast_sub h_ge]
  push_cast
  rfl

"""

content = content[:start_idx] + new_lemmas + content[end_idx:]

# 2. Swap odd and even lemmas dynamically
idx_odd = content.find("lemma padicValRat_two_sum_divisors_pow_two_odd")
idx_even = content.find("lemma padicValRat_two_sum_divisors_pow_two_even")
idx_next = content.find("lemma padicValRat_nonneg_of_den_eq_one")

if idx_odd == -1 or idx_even == -1 or idx_next == -1:
    print("Error: Swap markers not found!")
    exit(1)

block_odd = content[idx_odd:idx_even]
block_even = content[idx_even:idx_next]

# clean block_odd "padicValRat.one 2"
block_odd = block_odd.replace("padicValRat.one 2", "padicValRat.one")
block_odd = block_odd.replace("sigma_one_pos (2*k+1) (by omega)", "sigma_one_pos (2^(2*k+1)) (by positivity)")
block_odd = block_odd.replace("padicValRat_add_of_val_zero A B hA_val hB_val h_add_nz", "padicValRat_add_of_val_zero A B hA_nz hB_nz hA_val hB_val h_add_nz")

new_content = content[:idx_odd] + block_even + block_odd + content[idx_next:]

with open(dest, "w") as f:
    f.write(new_content)

print("Restore and fix completed successfully!")
