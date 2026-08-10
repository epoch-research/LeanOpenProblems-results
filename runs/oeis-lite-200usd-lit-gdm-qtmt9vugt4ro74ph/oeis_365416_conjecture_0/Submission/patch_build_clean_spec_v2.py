import os

def main():
    # 1. Read build_clean_spec.py
    with open("/workspace/leanproject/Submission/build_clean_spec.py", "r") as f:
        code = f.read()

    # 2. Define the new helper lemmas to insert
    new_helpers = """
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

lemma zmod_cast_8 (p r : ℕ) (h : p % 8 = r) : (p : ZMod 8) = (r : ZMod 8) := by
  have h_cast : ((p : ℕ) : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
  rw [h_cast, h]

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
    have : (3 : ZMod M) ^ 2 = 9 := by ring
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
"""

    # Insert new_helpers at the end of helper_lemmas
    code = code.replace(
        '  interval_cases h_cases : e % 41 <;> decide\n"""',
        '  interval_cases h_cases : e % 41 <;> decide\n' + new_helpers + '"""'
    )

    # 3. Locate and replace the else: block inside range(252)
    import re
    pattern = r'            else:\s+M_val = coprime_moduli\[r\].*?revert h_zmod_M <;> decide"\)'
    
    new_else_block = """            else:
                M_val = coprime_moduli[r]
                phi = 6 if M_val == 9 else (36 if M_val == 63 else (36 if M_val == 84 else 72))
                p3_code.append(f"        · -- q % 252 = {r}")
                p3_code.append(f"          have h_zmod_M : (q : ZMod {M_val}) ^ f - (3 : ZMod {M_val}) ^ e = 2 := zmod_equation 3 q e f {M_val} h")
                p3_code.append(f"          rw [zmod_cast_of_dvd q 252 {M_val} {r} (by decide) q_mod] at h_zmod_M")
                p3_code.append(f"          rw [pow_mod_period ({r % M_val} : ZMod {M_val}) f {phi} (by decide)] at h_zmod_M")
                p3_code.append(f"          rw [pow_three_period e {M_val} (by omega) (by decide)] at h_zmod_M")
                p3_code.append(f"          exact no_sol_contradiction {M_val} {phi} {r % M_val} f e (by decide) h_zmod_M (by decide)\")"""

    code = re.sub(pattern, new_else_block, code, flags=re.DOTALL)

    # 4. Write back to build_clean_spec.py
    with open("/workspace/leanproject/Submission/build_clean_spec.py", "w") as f:
        f.write(code)
    print("build_clean_spec.py successfully patched v2!")

if __name__ == "__main__":
    main()
