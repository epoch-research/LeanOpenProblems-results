import os
import re

def main():
    # Read the existing generate_short_spec.py
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        content = f.read()

    # Define the helper lemmas from unsafe_test3.lean
    helper_lemmas = """
lemma odd_sq_mod_eight (y : ℕ) (hy : y % 2 = 1) : 8 ∣ y ^ 2 - 1 := by
  have h_mod : y % 8 < 8 := Nat.mod_lt _ (by decide)
  set k := y / 8
  interval_cases y_mod : y % 8
  · have : y % 2 = 0 := by
      have : y = 8 * k + 0 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 1 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 2 * k) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 2 * k) + 1 - 1 = 8 * (8 * k ^ 2 + 2 * k) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 2 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 3 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 6 * k + 1) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 6 * k + 1) + 1 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 4 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 5 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 10 * k + 3) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 10 * k + 3) + 1 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 6 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 7 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 14 * k + 6) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 14 * k + 6) + 1 - 1 = 8 * (8 * k ^ 2 + 14 * k + 6) := by omega
    rw [this]
    exact dvd_mul_right 8 _

lemma pow_five_zmod_eight (e : ℕ) : (5 : ZMod 8) ^ e = 1 ∨ (5 : ZMod 8) ^ e = 5 := by
  induction e with
  | zero => left; rfl
  | succ e ih =>
    rcases ih with h1 | h2
    · right; rw [pow_succ, h1, one_mul]
    · left; rw [pow_succ, h2]
      decide

lemma hy_odd_proof (q f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (hf : f % 2 = 0) (hf_pos : f > 0) :
    (q ^ (f / 2)) % 2 = 1 := by
  set y := q ^ (f / 2)
  by_contra hc
  have hc_even : y % 2 = 0 := by omega
  have h_even_y : 2 ∣ y := Nat.dvd_of_mod_eq_zero hc_even
  have h_even_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even_y
  rcases hq.eq_one_or_self_of_dvd 2 h_even_q with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma f_even_contradiction (e f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_sq : q ^ f = 5 ^ e + 2) (hf_even : f % 2 = 0) (hf_pos : f > 0) : False := by
  have hf_eq : f = (f / 2) * 2 := by omega
  set y := q ^ (f / 2)
  have h_fy : q ^ f = y ^ 2 := by
    rw [hf_eq, pow_mul]
  have h_sq_y : y ^ 2 = 5 ^ e + 2 := by
    rw [← h_fy, h_sq]
  have hy_odd : y % 2 = 1 := hy_odd_proof q f hq hq_ne_2 hf_even hf_pos
  have h_dvd : 8 ∣ y ^ 2 - 1 := odd_sq_mod_eight y hy_odd
  have h_dvd_five : 8 ∣ 5 ^ e + 1 := by
    have h_sub : y ^ 2 - 1 = 5 ^ e + 1 := by
      generalize 5 ^ e = V at h_sq_y ⊢
      rw [h_sq_y]
      omega
    rw [h_sub] at h_dvd
    exact h_dvd
  have h_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = 0 := by
    rcases h_dvd_five with ⟨c, hc⟩
    have hc_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = ((8 * c : ℕ) : ZMod 8) := congrArg Nat.cast hc
    rw [hc_cast]
    push_cast
    have : (8 : ZMod 8) = 0 := rfl
    rw [this, zero_mul]
  have h_five_zmod : (5 : ZMod 8) ^ e = -1 := by
    have h_cast_push : (5 : ZMod 8) ^ e + 1 = 0 := by
      calc (5 : ZMod 8) ^ e + 1 = ((5 ^ e + 1 : ℕ) : ZMod 8) := by push_cast; rfl
      _ = 0 := h_cast
    calc (5 : ZMod 8) ^ e = (5 : ZMod 8) ^ e + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h_cast_push]
    _ = -1 := by ring
  have h_pow_cases := pow_five_zmod_eight e
  rcases h_pow_cases with h1 | h2
  · rw [h1] at h_five_zmod
    have : (1 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide
  · rw [h2] at h_five_zmod
    have : (5 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide

lemma pow_two_zmod_three_odd (e : ℕ) (he_odd : e % 2 = 1) : (2 : ZMod 3) ^ e = 2 := by
  have h_eq : e = 2 * (e / 2) + 1 := by omega
  rw [h_eq]
  have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
    rw [pow_succ, pow_mul]
  rw [this]
  have : (2 : ZMod 3) ^ 2 = 1 := rfl
  rw [this, one_pow, one_mul]

lemma q_mod_3_contradiction (e f q : ℕ) (hq_mod : q % 3 = 2) (he_odd : e % 2 = 1) (h : q ^ f = 5 ^ e + 2) : f % 2 = 0 := by
  by_contra hf_odd_hc
  have hf_odd : f % 2 = 1 := by omega
  have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((5 ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h
  push_cast at h_cast
  have hq_cast : (q : ZMod 3) = 2 := by
    have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hq_mod]
    rfl
  have h5_cast : (5 : ZMod 3) = 2 := rfl
  rw [hq_cast, h5_cast] at h_cast
  have hq_pow : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
  have h5_pow : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
  rw [hq_pow, h5_pow] at h_cast
  have : (2 : ZMod 3) = 2 + 2 := h_cast
  revert this
  decide
"""

    # Insert helper_lemmas assembly step in generate_short_spec.py
    assembly_target = '    out.append(test_content)'
    assembly_replacement = assembly_target + f'\\n    out.append("""{helper_lemmas}""")'
    content = content.replace(assembly_target, assembly_replacement)

    # Let's perform the regex substitutions for by omega; omega in the string literal pillai_diff_two_code in content
    # We find the start of pillai_diff_two_code definition
    # Let's write a python snippet inside generate_short_spec.py that does this substitution dynamically when generate_short_spec.py is run.
    # This is much safer than modifying the huge python string literal directly.
    # Where does generate_short_spec.py write pillai_diff_two_code?
    # out.append(pillai_diff_two_code)
    # We can replace out.append(pillai_diff_two_code) with out.append(fix_short_spec(pillai_diff_two_code))
    
    fixing_code = """
    # Dynamically fix pillai_diff_two_code before appending
    import re
    def fix_semicolons(text):
        pattern = r"^(\s*)· exfalso;\s*have\s*:\s*(.*?)\s*:=\s*by\s*omega;\s*omega$"
        def repl(match):
            spaces = match.group(1)
            prop = match.group(2)
            return f"{spaces}· exfalso\\n{spaces}  have : {prop} := by omega\\n{spaces}  omega"
        return re.sub(pattern, repl, text, flags=re.MULTILINE)

    pillai_diff_two_code = fix_semicolons(pillai_diff_two_code)

    old_block = \"\"\"                      have hq1 : (q : ZMod 3) = 1 := by
                        have : q % 3 = 1 := hq3_val
                        have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                        rw [h_cast, this]
                        rfl
                      have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
                      have h5e : (5 : ZMod 3) ^ e = 2 := by
                        have : (5 : ZMod 3) = 2 := rfl
                        rw [this]
                        have h_eq : e = 2 * (e / 2) + 1 := by omega
                        rw [h_eq]
                        have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                          rw [pow_succ, pow_mul]
                        rw [this]
                        have : (2 : ZMod 3) ^ 2 = 1 := rfl
                        rw [this, one_pow, one_mul]
                      rw [hq1, one_pow, h5e] at h_zmod_local
                      revert h_zmod_local; decide\"\"\"

    new_block = \"\"\"                      have h_zmod_8_local : (q : ZMod 8) ^ f - (5 : ZMod 8) ^ e = 2 := h_zmod8
                      have hq1 : (q : ZMod 8) = 1 := by
                        have : q % 8 = 1 := hq8_val
                        have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                        rw [h_cast, this]
                        rfl
                      have h5e8 : (5 : ZMod 8) ^ e = 5 := by
                        have : (5 : ZMod 8) = 5 := rfl
                        rw [this]
                        have h_eq : e = 2 * (e / 2) + 1 := by omega
                        rw [h_eq]
                        have : (5 : ZMod 8) ^ (2 * (e / 2) + 1) = ((5 : ZMod 8) ^ 2) ^ (e / 2) * 5 := by
                          rw [pow_succ, pow_mul]
                        rw [this]
                        have : (5 : ZMod 8) ^ 2 = 1 := rfl
                        rw [this, one_pow, one_mul]
                      rw [hq1, one_pow, h5e8] at h_zmod_8_local
                      revert h_zmod_8_local; decide\"\"\"

    pillai_diff_two_code = pillai_diff_two_code.replace(old_block, new_block)
    
    out.append(pillai_diff_two_code)
"""
    content = content.replace("    out.append(pillai_diff_two_code)", fixing_code)

    with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
        f.write(content)

if __name__ == "__main__":
    main()
