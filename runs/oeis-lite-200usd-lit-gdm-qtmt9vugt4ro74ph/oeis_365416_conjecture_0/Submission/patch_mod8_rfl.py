with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
    code = f.read()

# 1. Define the replacement for hp_mod : p % 8
old_hp = """                  interval_cases hp_mod : p % 8
                  · exact False.elim (dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod))
                  · rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rfl"""

new_hp = """                  interval_cases hp_mod : p % 8
                  · exact False.elim (dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod))
                  · rw [zmod_cast_8 p 1 hp_mod]; rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 p 3 hp_mod]; rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 p 5 hp_mod]; rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 p 7 hp_mod]; rfl"""

code = code.replace(old_hp, new_hp)

# 2. Define the replacement for hq_mod : q % 8
old_hq = """                  interval_cases hq_mod : q % 8
                  · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))
                  · rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · rfl"""

new_hq = """                  interval_cases hq_mod : q % 8
                  · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))
                  · rw [zmod_cast_8 q 1 hq_mod]; rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 q 3 hq_mod]; rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 q 5 hq_mod]; rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 q 7 hq_mod]; rfl"""

code = code.replace(old_hq, new_hq)

# 3. Define the second hq_mod : q % 8 (at line 364 of original file, but wait, is it identical?)
# Let's check: yes, it has same format but different indentation:
old_hq2 = """                interval_cases hq_mod : q % 8
                · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))
                · rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · rfl"""

new_hq2 = """                interval_cases hq_mod : q % 8
                · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))
                · rw [zmod_cast_8 q 1 hq_mod]; rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · rw [zmod_cast_8 q 3 hq_mod]; rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · rw [zmod_cast_8 q 5 hq_mod]; rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · rw [zmod_cast_8 q 7 hq_mod]; rfl"""

code = code.replace(old_hq2, new_hq2)

# 4. Define the replacement for hq8_val : q % 8
old_hq8_val = """                    interval_cases hq8_val : q % 8
                    · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val))
                    · rfl
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · rfl
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · rfl
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · rfl"""

new_hq8_val = """                    interval_cases hq8_val : q % 8
                    · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val))
                    · rw [zmod_cast_8 q 1 hq8_val]; rfl
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · rw [zmod_cast_8 q 3 hq8_val]; rfl
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · rw [zmod_cast_8 q 5 hq8_val]; rfl
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · rw [zmod_cast_8 q 7 hq8_val]; rfl"""

code = code.replace(old_hq8_val, new_hq8_val)

with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
    f.write(code)

print("generate_short_spec.py mod8 rfls successfully patched!")
