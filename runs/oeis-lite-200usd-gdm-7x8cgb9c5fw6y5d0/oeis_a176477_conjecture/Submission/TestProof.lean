import FormalConjectures.Util.ProblemImports

open Nat

def den : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (2 * (k + 2) + 1) ^ 3 * den (k + 1)

def num : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let term1 := 32 * n_idx ^ 3 * num (k + 1)
    let P_n := 21 * n_idx ^ 3 + 22 * n_idx ^ 2 + 8 * n_idx + 1
    let binom_pow4 := (Nat.choose (2 * n_idx - 1) n_idx) ^ 4
    term1 + P_n * binom_pow4 * den (k + 1)

lemma den_pos (n : ℕ) : den n > 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _|k
    · decide
    · -- den (k + 2)
      have : k + 2 = k + 1 + 1 := rfl
      rw [this]
      rw [den]
      positivity

lemma den_odd (n : ℕ) : den n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _|k
    · decide
    · -- den (k + 2)
      have : k + 2 = k + 1 + 1 := rfl
      rw [this]
      rw [den]
      have h_odd : (2 * (k + 1 + 1) + 1) ^ 3 = 2 * (4 * k ^ 3 + 30 * k ^ 2 + 75 * k + 62) + 1 := by ring
      rw [h_odd]
      have h_ring : (2 * (4 * k ^ 3 + 30 * k ^ 2 + 75 * k + 62) + 1) * den (k + 1) = 
                    2 * ((4 * k ^ 3 + 30 * k ^ 2 + 75 * k + 62) * den (k + 1)) + den (k + 1) := by ring
      rw [h_ring]
      omega

lemma pow4_mod_two (x : ℕ) : x ^ 4 % 2 = x % 2 := by
  have h_mod := Nat.mod_two_eq_zero_or_one x
  rcases h_mod with h | h
  · have : ∃ d, x = 2 * d := ⟨x / 2, by omega⟩
    rcases this with ⟨d, rfl⟩
    have : (2 * d) ^ 4 = 2 * (8 * d ^ 4) := by ring
    omega
  · have : ∃ d, x = 2 * d + 1 := ⟨x / 2, by omega⟩
    rcases this with ⟨d, rfl⟩
    have : (2 * d + 1) ^ 4 = 2 * (8 * d ^ 4 + 16 * d ^ 3 + 12 * d ^ 2 + 4 * d) + 1 := by ring
    omega

lemma choose_two_mul_sub_one_self_modEq (d : ℕ) (hd : d ≥ 1) :
    choose (2 * d - 1) d ≡ choose (d - 1) (d / 2) [MOD 2] := by
  have hd_cases : d = 1 ∨ d ≥ 2 := by omega
  rcases hd_cases with rfl | hd_ge2
  · rfl
  · have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h_choose := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * d - 1) (k := d) (p := 2)
    have h_num : (2 * d - 1) % 2 = 1 := by omega
    have h_den : (2 * d - 1) / 2 = d - 1 := by omega
    rw [h_num, h_den] at h_choose
    have hd_mod : d % 2 = 0 ∨ d % 2 = 1 := Nat.mod_two_eq_zero_or_one d
    rcases hd_mod with hd_even | hd_odd
    · rw [hd_even] at h_choose
      have h_choose_1_0 : choose 1 0 = 1 := by decide
      rw [h_choose_1_0, one_mul] at h_choose
      exact h_choose
    · rw [hd_odd] at h_choose
      have h_choose_1_1 : choose 1 1 = 1 := by decide
      rw [h_choose_1_1, one_mul] at h_choose
      exact h_choose

lemma choose_two_mul_self_even (d : ℕ) (hd : d ≥ 1) :
    choose (2 * d) d ≡ 0 [MOD 2] := by
  have h_choose : choose (2 * d) d = choose (2 * d - 1) (d - 1) + choose (2 * d - 1) d := by
    have h_eq : choose (2 * d) d = choose (succ (2 * d - 1)) (succ (d - 1)) := by congr 1 <;> omega
    rw [h_eq, Nat.choose_succ_succ]
    have : succ (d - 1) = d := by omega
    rw [this]
  have h_symm : choose (2 * d - 1) (d - 1) = choose (2 * d - 1) d := Nat.choose_symm_of_eq_add (by omega)
  rw [h_choose, h_symm]
  have h_double : choose (2 * d - 1) d + choose (2 * d - 1) d = 2 * choose (2 * d - 1) d := by ring
  rw [h_double]
  have : (2 * choose (2 * d - 1) d) % 2 = 0 := Nat.mul_mod_right 2 (choose (2 * d - 1) d)
  exact this

lemma odd_pow_three_odd (x : ℕ) (hx : x % 2 = 1) : (x ^ 3) % 2 = 1 := by
  have : ∃ d, x = 2 * d + 1 := ⟨x / 2, by omega⟩
  rcases this with ⟨d, rfl⟩
  have : (2 * d + 1) ^ 3 = 2 * (4 * d ^ 3 + 6 * d ^ 2 + 3 * d) + 1 := by ring
  rw [this]
  omega

lemma num_mod_two_eq (n : ℕ) (hn : n ≥ 2) : num n % 2 = (choose (n-1) (n/2) * den n) % 2 := by
  rcases n with _|n
  · contradiction
  rcases n with _|k
  · contradiction
  · -- n = k + 2
    have h_num : num (k + 2) = 32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := rfl
    have h_den : den (k + 2) = (2 * (k + 2) + 1) ^ 3 * den (k + 1) := rfl
    rw [h_num, h_den]
    -- We want to show LHS % 2 = RHS % 2
    have h_lhs : (32 * (k + 2) ^ 3 * num (k + 1) + (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 =
                 ((21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 := by
      have h32 : 32 * (k + 2) ^ 3 * num (k + 1) = 2 * (16 * (k + 2) ^ 3 * num (k + 1)) := by ring
      rw [h32]
      omega
    rw [h_lhs]
    have h_P_mod : (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) % 2 = ((k + 2) ^ 3 + 1) % 2 := by
      have h_eq : 21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1 = 2 * (10 * (k + 2) ^ 3 + 11 * (k + 2) ^ 2 + 4 * (k + 2)) + ((k + 2) ^ 3 + 1) := by ring
      rw [h_eq]
      omega
    -- Now rcases on k+2 % 2 = 0 or 1
    have hk_even_odd : (k + 2) % 2 = 0 ∨ (k + 2) % 2 = 1 := Nat.mod_two_eq_zero_or_one (k + 2)
    rcases hk_even_odd with hk_even | hk_odd
    · -- k + 2 is even
      have : ∃ d, k + 2 = 2 * d := ⟨(k + 2) / 2, by omega⟩
      rcases this with ⟨d, hd_eq⟩
      have hd_ge1 : d ≥ 1 := by omega
      have h_cube_mod : ((k + 2) ^ 3 + 1) % 2 = 1 := by
        have : (k + 2) ^ 3 + 1 = 2 * (4 * d ^ 3) + 1 := by
          rw [hd_eq]
          ring
        omega
      have h_lhs_simp : ((21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 =
                        (choose (k + 1) ((k + 2) / 2) * den (k + 1)) % 2 := by
        have h_P : 21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1 = 2 * (84 * d ^ 3 + 44 * d ^ 2 + 8 * d) + 1 := by
          rw [hd_eq]
          ring
        rw [h_P]
        have h_pow4 : (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 % 2 = (choose (2 * (k + 2) - 1) (k + 2)) % 2 := pow4_mod_two _
        have h_choose_eq : (choose (2 * (k + 2) - 1) (k + 2)) % 2 = (choose (k + 1) ((k + 2) / 2)) % 2 := by
          have hk1 : k + 1 = 2 * d - 1 := by omega
          have hk2 : (k + 2) / 2 = d := by omega
          rw [hk2, hd_eq, hk1]
          have h_div : 2 * d / 2 = d := by omega
          have h_mod := choose_two_mul_sub_one_self_modEq (2 * d) (by omega)
          rw [h_div] at h_mod
          exact h_mod
        have h_ring : (2 * (84 * d ^ 3 + 44 * d ^ 2 + 8 * d) + 1) * (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) =
                      2 * ((84 * d ^ 3 + 44 * d ^ 2 + 8 * d) * (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) + (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) := by ring
        rw [h_ring]
        have h_omega : (2 * ((84 * d ^ 3 + 44 * d ^ 2 + 8 * d) * (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) + (choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 =
                       ((choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 := by omega
        rw [h_omega]
        rw [Nat.mul_mod, h_pow4, h_choose_eq, ← Nat.mul_mod]
      rw [h_lhs_simp]
      have h_rhs : (choose (k + 1) ((k + 2) / 2) * (2 * (k + 2) + 1) ^ 3 * den (k + 1)) % 2 =
                   (choose (k + 1) ((k + 2) / 2) * den (k + 1)) % 2 := by
        have h_pow3 : (2 * (k + 2) + 1) ^ 3 = 2 * (4 * (k + 2) ^ 3 + 6 * (k + 2) ^ 2 + 3 * (k + 2)) + 1 := by ring
        have h_ring : choose (k + 1) ((k + 2) / 2) * (2 * (k + 2) + 1) ^ 3 * den (k + 1) =
                      2 * (choose (k + 1) ((k + 2) / 2) * (4 * (k + 2) ^ 3 + 6 * (k + 2) ^ 2 + 3 * (k + 2)) * den (k + 1)) + choose (k + 1) ((k + 2) / 2) * den (k + 1) := by
          rw [h_pow3]
          ring
        rw [h_ring]
        omega
      have h_simpl : choose (k + 1 + 1 - 1) ((k + 1 + 1) / 2) = choose (k + 1) ((k + 2) / 2) := rfl
      rw [h_simpl, ← Nat.mul_assoc]
      rw [h_rhs]
    · -- k + 2 is odd
      have : ∃ d, k + 2 = 2 * d + 1 := ⟨(k + 2) / 2, by omega⟩
      rcases this with ⟨d, hd_eq⟩
      have hd_ge1 : d ≥ 1 := by omega
      have h_cube_mod : ((k + 2) ^ 3 + 1) % 2 = 0 := by
        have : (k + 2) ^ 3 + 1 = 2 * (4 * d ^ 3 + 6 * d ^ 2 + 3 * d + 1) := by
          rw [hd_eq]
          ring
        omega
      have h_lhs_zero : ((21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) % 2 = 0 := by
        have h_P : 21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1 = 2 * (84 * d ^ 3 + 170 * d ^ 2 + 115 * d + 26) := by
          rw [hd_eq]
          ring
        have h_ring : (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1) =
                      2 * ((84 * d ^ 3 + 170 * d ^ 2 + 115 * d + 26) * (Nat.choose (2 * (k + 2) - 1) (k + 2)) ^ 4 * den (k + 1)) := by
          rw [h_P]
          ring
        rw [h_ring]
        exact Nat.mul_mod_right _ _
      rw [h_lhs_zero]
      have h_choose_even : choose (k + 1) ((k + 2) / 2) % 2 = 0 := by
        have hk_eq : k + 1 = 2 * d := by omega
        rw [hd_eq, hk_eq]
        have h_div : (2 * d + 1) / 2 = d := by omega
        rw [h_div]
        have h_choose := choose_two_mul_self_even d hd_ge1
        exact h_choose
      have h_simpl : choose (k + 1 + 1 - 1) ((k + 1 + 1) / 2) = choose (k + 1) ((k + 2) / 2) := rfl
      rw [h_simpl]
      rw [Nat.mul_mod, h_choose_even, zero_mul, Nat.zero_mod]
