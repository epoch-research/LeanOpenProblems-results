import FormalConjectures.Util.ProblemImports
open Nat

def NoSol (M phi r : ℕ) : Prop :=
  ∀ f_mod < phi, ∀ e_mod < 6, (r : ZMod M) ^ f_mod - (3 : ZMod M) ^ (e_mod + 2) ≠ 2

instance (M phi r : ℕ) : Decidable (NoSol M phi r) := by
  dsimp [NoSol]
  infer_instance

lemma zmod_cast_of_dvd (q M N r : ℕ) (h_dvd : N ∣ M) (hq_mod : q % M = r) :
    (q : ZMod N) = ((r % N : ℕ) : ZMod N) := by
  have h_eq : q = M * (q / M) + r := by
    have := (Nat.div_add_mod q M).symm
    rw [hq_mod] at this
    exact this
  have h_cast : (q : ZMod N) = ((M * (q / M) + r : ℕ) : ZMod N) := congrArg Nat.cast h_eq
  rw [h_cast]
  push_cast
  rcases h_dvd with ⟨k, rfl⟩
  have h_mul_zero : ((N * k : ℕ) : ZMod N) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  rw [h_mul_zero, zero_mul, zero_add]
  have h_mod : ((r : ℕ) : ZMod N) = ((r % N : ℕ) : ZMod N) := by
    nth_rw 1 [← Nat.div_add_mod r N]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  exact h_mod

lemma zmod_equation (p q e f M : ℕ) (h : q ^ f - p ^ e = 2) :
    (q : ZMod M) ^ f - (p : ZMod M) ^ e = 2 := by
  have h_ge : q ^ f ≥ p ^ e := by omega
  have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod M) = ((2 : ℕ) : ZMod M) := congrArg Nat.cast h
  rw [Nat.cast_sub h_ge] at h_cast
  push_cast at h_cast
  exact h_cast

lemma pow_mod_period (B : ZMod M) (f P : ℕ) (hP : B ^ P = 1) :
    B ^ f = B ^ (f % P) := by
  have h_eq : f = P * (f / P) + f % P := (Nat.div_add_mod f P).symm
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul, hP, one_pow, one_mul]

lemma pow_three_period (e M : ℕ) (he : 1 < e) (h_decide : (3 : ZMod M) ^ 6 * 9 = 9) :
    (3 : ZMod M) ^ e = (3 : ZMod M) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + ((e - 2) % 6 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add]
  have h_eq2 : (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 9 * (3 : ZMod M) ^ ((e - 2) % 6) := by
    have : (e - 2) % 6 + 2 = 2 + (e - 2) % 6 := by omega
    rw [this, pow_add]
    have : (3 : ZMod M) ^ 2 = 9 := by
      ring
    rw [this]
  rw [h_eq2]
  have h_assoc : (3 : ZMod M) ^ (6 * ((e - 2) / 6)) * (9 * 3 ^ ((e - 2) % 6)) =
      ((3 : ZMod M) ^ (6 * ((e - 2) / 6)) * 9) * 3 ^ ((e - 2) % 6) := by ring
  rw [h_assoc]
  have pow_three_helper : ∀ k : ℕ, (3 : ZMod M) ^ (6 * k) * 9 = 9 := by
    intro k
    induction k with
    | zero => simp only [mul_zero, pow_zero, one_mul]
    | succ k ih =>
      have h_step : 6 * (k + 1) = 6 * k + 6 := by ring
      rw [h_step, pow_add]
      have h_assoc2 : (3 : ZMod M) ^ (6 * k) * 3 ^ 6 * 9 = (3 : ZMod M) ^ (6 * k) * (3 ^ 6 * 9) := by ring
      rw [h_assoc2, h_decide, ih]
  rw [pow_three_helper, ← h_eq2]

lemma no_sol_contradiction (M phi r f e : ℕ) (phi_pos : 0 < phi)
    (h_zmod : (r : ZMod M) ^ (f % phi) - (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 2)
    (h_no_sol : NoSol M phi r) : False := by
  have hf_mod : f % phi < phi := Nat.mod_lt _ phi_pos
  have he_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)
  exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod

-- Test the decide tactic on NoSol
lemma test_no_sol_9_1 : NoSol 9 6 1 := by decide

lemma test_omega (q : ℕ) (hq_mod : q % 8 = 2) : q % 2 = 0 := by omega

lemma test_omega25 (q : ℕ) (hq_mod : q % 25 = 1) : q % 5 = 1 := by omega

lemma zmod_cast_8 (p r : ℕ) (h : p % 8 = r) : (p : ZMod 8) = (r : ZMod 8) := by
  have h_cast : ((p : ℕ) : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
  rw [h_cast, h]

lemma test_rfl (p : ℕ) (hp_mod : p % 8 = 3) : (p : ZMod 8) ^ 2 = 1 := by
  rw [zmod_cast_8 p 3 hp_mod]
  rfl

lemma lt_cases_exception (q e f E_val R_val M_val : ℕ) (hq_ge : q ≥ M_val) (he_ge : e ≥ 3) (he_ne : e ≠ E_val) (hf : f > 0)
    (h_eq : q ^ f = 3 ^ e + 2) (h_lt : 3 ^ (E_val - 1) + 2 < M_val) (h_E : E_val ≥ 3) : e ≥ E_val + 1 := by
  by_contra hc
  have he_lt : e < E_val := by omega
  have he_le : e ≤ E_val - 1 := by omega
  have h_pow : 3 ^ e + 2 ≤ 3 ^ (E_val - 1) + 2 := by
    have : 3 ^ e ≤ 3 ^ (E_val - 1) := Nat.pow_le_pow_right (by decide) he_le
    omega
  have : q ^ f < M_val := by
    calc q ^ f = 3 ^ e + 2 := h_eq
    _ ≤ 3 ^ (E_val - 1) + 2 := h_pow
    _ < M_val := h_lt
  have : q ^ f ≥ M_val := by
    calc q ^ f ≥ q ^ 1 := Nat.pow_le_pow_right (by omega) hf
    _ = q := pow_one q
    _ ≥ M_val := hq_ge
  omega
