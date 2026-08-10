with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
    code = f.read()

# 1. Fix the hf_even2 bug at line 606-607
old_block_1 = """            have hf_even2 : f % 2 = 0 := hf_even
            have h_sq : q ^ f = 5 ^ e + 2 := by omega\\n            exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even2 (by omega)"""

new_block_1 = """            have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
            have hq2 : (q : ZMod 3) = 2 := by
              have : q % 3 = 2 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have h5_2 : (5 : ZMod 3) = 2 := rfl
            have hqf : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
            have h5e : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
            rw [hq2, h5_2] at h_zmod_local
            rw [hqf, h5e] at h_zmod_local
            revert h_zmod_local; decide"""

# Replace (using simple replacement or regex to handle exact indentation/whitespace)
code = code.replace(old_block_1, new_block_1)

# Double check if literal \\n version exists
old_block_1_v2 = """            have hf_even2 : f % 2 = 0 := hf_even
            have h_sq : q ^ f = 5 ^ e + 2 := by omega\n            exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even2 (by omega)"""
code = code.replace(old_block_1_v2, new_block_1)

# 2. Fix the rcases hf_even2 bug at line 872
old_block_2 = "rcases hf_even2 with hf0 | hf2 <;> rw [hf0, hf2] at h_zmod5 <;> revert h_zmod5 <;> decide"
new_block_2 = """rcases hf_even2 with hf0 | hf2
                · rw [hf0] at h_zmod5; revert h_zmod5; decide
                · rw [hf2] at h_zmod5; revert h_zmod5; decide"""

code = code.replace(old_block_2, new_block_2)

with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
    f.write(code)

print("generate_short_spec.py successfully fixed!")
