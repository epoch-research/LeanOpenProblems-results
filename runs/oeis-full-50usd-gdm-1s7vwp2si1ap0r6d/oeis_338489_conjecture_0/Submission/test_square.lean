import FormalConjectures.Util.ProblemImports
open Nat

def is_square_dec (n : ℕ) : Bool :=
  let s := n.sqrt
  s * s == n

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

lemma k_mul_k_add_one_even (k : ℕ) : 2 ∣ k * (k + 1) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · use m * (2 * m + 1)
    ring
  · use (2 * m + 1) * (m + 1)
    ring

lemma k_mul_k_add_one_div_two_mul_two (k : ℕ) : (k * (k + 1) / 2) * 2 = k * (k + 1) := by
  have hdvd : 2 ∣ k * (k + 1) := k_mul_k_add_one_even k
  exact Nat.div_mul_cancel hdvd

lemma is_triangular_iff_square (x : ℕ) : is_triangular x ↔ is_square_dec (8 * x + 1) = true := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [is_square_dec]
    have h1 : 8 * (k * (k + 1) / 2) + 1 = (2 * k + 1) * (2 * k + 1) := by
      have : 8 * (k * (k + 1) / 2) = 4 * ((k * (k + 1) / 2) * 2) := by ring
      rw [this, k_mul_k_add_one_div_two_mul_two]
      ring
    rw [h1, Nat.sqrt_eq, beq_iff_eq]
  · rw [is_square_dec, beq_iff_eq]
    intro h
    let s := (8 * x + 1).sqrt
    have hs : s * s = 8 * x + 1 := h
    have h_odd : s % 2 = 1 := by
      have h2 : (s * s) % 2 = (8 * x + 1) % 2 := by rw [hs]
      have h3 : (8 * x + 1) % 2 = 1 := by omega
      rw [Nat.mul_mod, h3] at h2
      rcases Nat.mod_two_eq_zero_or_one s with h0 | h1
      · rw [h0, Nat.zero_mul, Nat.zero_mod] at h2; contradiction
      · exact h1
    have h_eq : s = 2 * (s / 2) + s % 2 := (Nat.div_add_mod s 2).symm
    rw [h_odd] at h_eq
    let k := s / 2
    have hs2 : s = 2 * k + 1 := h_eq
    have h4 : 4 * (k * (k + 1)) + 1 = 8 * x + 1 := by
      calc 4 * (k * (k + 1)) + 1 = (2 * k + 1) * (2 * k + 1) := by ring
        _ = s * s := by rw [hs2]
        _ = 8 * x + 1 := hs
    have h6 : k * (k + 1) = 2 * x := by omega
    use k
    have h7 : (k * (k + 1)) / 2 = (2 * x) / 2 := by rw [h6]
    rw [h7, Nat.mul_div_cancel_left x (by omega)]
