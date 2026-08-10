import FormalConjectures.Util.ProblemImports

open Nat

lemma mod_64_of_mod_480_eq_449 {B : ℕ} (h : B % 480 = 449) : B % 64 = 1 ∨ B % 64 = 33 := by
  have : B = 480 * (B / 480) + B % 480 := (Nat.div_add_mod B 480).symm
  rw [h] at this
  rw [this]
  have h_mod : B / 480 % 2 = 0 ∨ B / 480 % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hk]
    left
    have : 480 * (2 * k) + 449 = 449 + 64 * (15 * k) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 2 * k + 1 := ⟨B / 480 / 2, by omega⟩
    rw [hk]
    right
    have : 480 * (2 * k + 1) + 449 = 33 + 64 * (15 * k + 14) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]

lemma thirty_three_pow_odd (k : ℕ) : 33 ^ (2 * k + 1) % 64 = 33 := by
  have h_pow : 33 ^ (2 * k + 1) = 33 * 1089 ^ k := by
    rw [pow_succ, mul_comm]
    congr 1
    have : 33 ^ 2 = 1089 := rfl
    rw [pow_mul, this]
  rw [h_pow]
  have h_pow2 : 1089 ^ k % 64 = 1 := by
    have : 1089 ^ k % 64 = (1089 % 64) ^ k % 64 := Nat.pow_mod 1089 k 64
    have h_mod : 1089 % 64 = 1 := rfl
    rw [h_mod] at this
    simp only [Nat.one_pow] at this
    exact this
  rw [Nat.mul_mod, h_pow2]

lemma B_pow_mod_64_eq_33 (B p : ℕ) (hB : B % 64 = 33) (hp_odd : p % 2 = 1) : B ^ p % 64 = 33 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  have h_mod : B ^ (2 * k + 1) % 64 = (B % 64) ^ (2 * k + 1) % 64 := Nat.pow_mod B (2 * k + 1) 64
  rw [hB] at h_mod
  rw [h_mod]
  exact thirty_three_pow_odd k

lemma mod_128_of_mod_64_eq_1 {B : ℕ} (h : B % 64 = 1) : B % 128 = 1 ∨ B % 128 = 65 := by
  have : B = 64 * (B / 64) + B % 64 := (Nat.div_add_mod B 64).symm
  rw [h] at this
  rw [this]
  have h_mod : B / 64 % 2 = 0 ∨ B / 64 % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hk]
    left
    have : 64 * (2 * k) + 1 = 1 + 128 * k := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 64 = 2 * k + 1 := ⟨B / 64 / 2, by omega⟩
    rw [hk]
    right
    have : 64 * (2 * k + 1) + 1 = 65 + 128 * k := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]

lemma sixty_five_pow_odd (k : ℕ) : 65 ^ (2 * k + 1) % 128 = 65 := by
  have h_pow : 65 ^ (2 * k + 1) = 65 * 4225 ^ k := by
    rw [pow_succ, mul_comm]
    congr 1
    have : 65 ^ 2 = 4225 := rfl
    rw [pow_mul, this]
  rw [h_pow]
  have h_pow2 : 4225 ^ k % 128 = 1 := by
    have : 4225 ^ k % 128 = (4225 % 128) ^ k % 128 := Nat.pow_mod 4225 k 128
    have h_mod : 4225 % 128 = 1 := rfl
    rw [h_mod] at this
    simp only [Nat.one_pow] at this
    exact this
  rw [Nat.mul_mod, h_pow2]

lemma B_pow_mod_128_eq_65 (B p : ℕ) (hB : B % 128 = 65) (hp_odd : p % 2 = 1) : B ^ p % 128 = 65 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  have h_mod : B ^ (2 * k + 1) % 128 = (B % 128) ^ (2 * k + 1) % 128 := Nat.pow_mod B (2 * k + 1) 128
  rw [hB] at h_mod
  rw [h_mod]
  exact sixty_five_pow_odd k

lemma mod_256_of_mod_128_eq_1 {B : ℕ} (h : B % 128 = 1) : B % 256 = 1 ∨ B % 256 = 129 := by
  have : B = 128 * (B / 128) + B % 128 := (Nat.div_add_mod B 128).symm
  rw [h] at this
  rw [this]
  have h_mod : B / 128 % 2 = 0 ∨ B / 128 % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hk]
    left
    have : 128 * (2 * k) + 1 = 1 + 256 * k := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 128 = 2 * k + 1 := ⟨B / 128 / 2, by omega⟩
    rw [hk]
    right
    have : 128 * (2 * k + 1) + 1 = 129 + 256 * k := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]

lemma one_twenty_nine_pow_odd (k : ℕ) : 129 ^ (2 * k + 1) % 256 = 129 := by
  have h_pow : 129 ^ (2 * k + 1) = 129 * 16641 ^ k := by
    rw [pow_succ, mul_comm]
    congr 1
    have : 129 ^ 2 = 16641 := rfl
    rw [pow_mul, this]
  rw [h_pow]
  have h_pow2 : 16641 ^ k % 256 = 1 := by
    have : 16641 ^ k % 256 = (16641 % 256) ^ k % 256 := Nat.pow_mod 16641 k 256
    have h_mod : 16641 % 256 = 1 := rfl
    rw [h_mod] at this
    simp only [Nat.one_pow] at this
    exact this
  rw [Nat.mul_mod, h_pow2]

lemma B_pow_mod_256_eq_129 (B p : ℕ) (hB : B % 256 = 129) (hp_odd : p % 2 = 1) : B ^ p % 256 = 129 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  have h_mod : B ^ (2 * k + 1) % 256 = (B % 256) ^ (2 * k + 1) % 256 := Nat.pow_mod B (2 * k + 1) 256
  rw [hB] at h_mod
  rw [h_mod]
  exact one_twenty_nine_pow_odd k

lemma mod_of_mod_256 {X : ℕ} (h : X % 256 = 1) : X % 128 = 1 ∧ X % 64 = 1 := by
  have h_eq : X = 256 * (X / 256) + 1 := by
    have := Nat.div_add_mod X 256
    omega
  constructor
  · rw [h_eq]
    have : 256 * (X / 256) + 1 = 1 + 128 * (2 * (X / 256)) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · rw [h_eq]
    have : 256 * (X / 256) + 1 = 1 + 64 * (4 * (X / 256)) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]

lemma mod_32_of_mod_256 {X : ℕ} (h : X % 256 = 1) : X % 32 = 1 := by
  have h_eq : X = 256 * (X / 256) + 1 := by
    have := Nat.div_add_mod X 256
    omega
  rw [h_eq]
  have : 256 * (X / 256) + 1 = 1 + 32 * (8 * (X / 256)) := by ring
  rw [this]
  rw [Nat.add_mul_mod_self_left]
