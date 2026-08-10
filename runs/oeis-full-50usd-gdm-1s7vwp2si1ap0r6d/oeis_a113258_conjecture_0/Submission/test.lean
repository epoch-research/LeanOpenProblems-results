import FormalConjectures.Util.ProblemImports

set_option autoImplicit false

open Nat

-- we assume a is defined
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

lemma a_split (n : ℕ) (hn : n ≥ 2) :
    a n = (1) ^ (n.factorial) + 2 ^ ((n - 1).factorial) +
      Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2))) := by
  sorry

lemma a_mod_256 (n : ℕ) : a (n + 11) % 256 = 1 := by
  sorry

lemma mod_of_mod_256 {X : ℕ} (h : X % 256 = 1) : X % 128 = 1 ∧ X % 64 = 1 := by
  sorry

lemma mod_32_of_mod_256 {X : ℕ} (h : X % 256 = 1) : X % 32 = 1 := by
  sorry

lemma thirty_three_pow_odd (k : ℕ) : 33 ^ (2 * k + 1) % 64 = 33 := by
  sorry

lemma B_pow_mod_64_eq_33 (b p : ℕ) (hb : b % 64 = 33) (hp_odd : p % 2 = 1) : b ^ p % 64 = 33 := by
  sorry

lemma sixty_five_pow_odd (k : ℕ) : 65 ^ (2 * k + 1) % 128 = 65 := by
  sorry

lemma B_pow_mod_128_eq_65 (b p : ℕ) (hb : b % 128 = 65) (hp_odd : p % 2 = 1) : b ^ p % 128 = 65 := by
  sorry

lemma mod_16_pow (b p : ℕ) (hp : p % 2 = 1) (hb : b % 16 = 9) : b ^ p % 16 = 9 := by
  sorry

lemma b_mod_128_eq_1 (b p n : ℕ) (h_eq : a (n + 11) = b ^ p) (hp_odd : p % 2 = 1)
    (h_b_mod3 : b % 3 = 2) (h_b_mod5 : b % 5 = 4) (h_b_mod8 : b % 8 = 1) : b % 128 = 1 := by
  have h_b_mod16_cases : b % 16 = 1 ∨ b % 16 = 9 := by omega
  rcases h_b_mod16_cases with hB16_1 | hB16_9
  · have h_b_mod32_cases : b % 32 = 1 ∨ b % 32 = 17 := by omega
    rcases h_b_mod32_cases with hB32_1 | hB32_17
    · have h_b_mod64_cases : b % 64 = 1 ∨ b % 64 = 33 := by omega
      rcases h_b_mod64_cases with hB64_1 | hB64_33
      · have h_b_mod128_cases : b % 128 = 1 ∨ b % 128 = 65 := by omega
        rcases h_b_mod128_cases with hB128_1 | hB128_65
        · exact hB128_1
        · sorry
      · sorry
    · sorry
  · sorry
