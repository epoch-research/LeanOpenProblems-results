import FormalConjectures.Util.ProblemImports

open Nat

lemma mod_3840_of_mod_256_and_480 {B : ℕ} (h1 : B % 256 = 1) (h2 : B % 480 = 449) : B % 3840 = 3329 := by
  have h_eq : B = 480 * (B / 480) + B % 480 := (Nat.div_add_mod B 480).symm
  rw [h2] at h_eq
  have h_mod : (B / 480) % 8 = 0 ∨ (B / 480) % 8 = 1 ∨ (B / 480) % 8 = 2 ∨ (B / 480) % 8 = 3 ∨ (B / 480) % 8 = 4 ∨ (B / 480) % 8 = 5 ∨ (B / 480) % 8 = 6 ∨ (B / 480) % 8 = 7 := by omega
  rcases h_mod with h0 | h1_cases | h2_cases | h3 | h4 | h5 | h6 | h7
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 0 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 0) + 449 = 193 + 256 * (15 * k + 1) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 1 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 1) + 449 = 161 + 256 * (15 * k + 3) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 2 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 2) + 449 = 129 + 256 * (15 * k + 5) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 3 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 3) + 449 = 97 + 256 * (15 * k + 7) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 4 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 4) + 449 = 65 + 256 * (15 * k + 9) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 5 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 5) + 449 = 33 + 256 * (15 * k + 11) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 6 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq]
    have : 480 * (8 * k + 6) + 449 = 3329 + 3840 * k := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 8 * k + 7 := ⟨B / 480 / 8, by omega⟩
    rw [hk] at h_eq
    rw [h_eq] at h1
    have : 480 * (8 * k + 7) + 449 = 225 + 256 * (15 * k + 14) := by ring
    rw [this] at h1
    rw [Nat.add_mul_mod_self_left] at h1
    contradiction
