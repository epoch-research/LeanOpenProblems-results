import re

def main():
    with open("/workspace/leanproject/Submission/build_clean_spec.py", "r") as f:
        content = f.read()

    # 1. Fix non_coprime_contradiction
    content = content.replace(
        "    exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_M _) h_g_dvd_r",
        "    exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_M (q / M)) h_g_dvd_r"
    )

    # 2. Fix pow_three_zmod_83
    old_pow83 = """lemma pow_three_zmod_83 (e : ℕ) : (3 : ZMod 83) ^ e = 81 ↔ e % 82 = 4 := by
  have h_eq : e = 82 * (e / 82) + e % 82 := (Nat.div_add_mod e 82).symm
  have h_pow : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 82) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 83) ^ 82 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 82 < 82 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 82 <;> decide"""

    new_pow83 = """lemma pow_three_zmod_83 (e : ℕ) : (3 : ZMod 83) ^ e = 81 ↔ e % 41 = 4 := by
  have h_eq : e = 41 * (e / 41) + e % 41 := (Nat.div_add_mod e 41).symm
  have h_pow : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 41) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 83) ^ 41 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 41 < 41 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 41 <;> decide"""

    content = content.replace(old_pow83, new_pow83)

    # 3. Fix hq23
    content = content.replace(
        '    p3_code.append("        by_cases hq23 : q = 23")\n    p3_code.append("        · subst hq23")\n    p3_code.append("          by_contra")\n    p3_code.append("          have h_zmod : (23 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")\n    p3_code.append("            have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("            have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")',
        '    p3_code.append("        by_cases hq23 : q = 23")\n    p3_code.append("        · subst hq23")\n    p3_code.append("          by_contra")\n    p3_code.append("          have h_zmod : (23 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")\n    p3_code.append("            have h_ge : 23 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("            have h_cast : ((23 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")'
    )

    content = content.replace(
        '    p3_code.append("          have h_cast2 : (3 : ZMod 11) ^ e = 10 := by")\n    p3_code.append("            calc (3 : ZMod 11) ^ e = - (- (3 : ZMod 11) ^ e) := by ring")\n    p3_code.append("            _ = -2 := by rw [h_zmod]")\n    p3_code.append("            _ = 10 := rfl")',
        '    p3_code.append("          have h_cast2 : (3 : ZMod 11) ^ e = 10 := by")\n    p3_code.append("            calc (3 : ZMod 11) ^ e = 1 - ((1 : ZMod 11) - (3 : ZMod 11) ^ e) := by ring")\n    p3_code.append("            _ = 1 - 2 := by rw [h_zmod]")\n    p3_code.append("            _ = 10 := rfl")'
    )

    # 4. Fix hq29
    content = content.replace(
        '    p3_code.append("            have h_zmod : (29 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")\n    p3_code.append("              have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")',
        '    p3_code.append("            have h_zmod : (29 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")\n    p3_code.append("              have h_ge : 29 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((29 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")'
    )

    # 5. Fix hq83
    content = content.replace(
        '    p3_code.append("            have h_zmod : (83 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")\n    p3_code.append("              have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")',
        '    p3_code.append("            have h_zmod : (83 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")\n    p3_code.append("              have h_ge : 83 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((83 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")'
    )

    # 6. Fix hq113 decide
    # Let's find hq113 dec_eq block
    content = content.replace(
        '    p3_code.append("            have h_div : e = 112 * (e / 112) + 68 := by")\n    p3_code.append("              have := Nat.div_add_mod e 112")\n    p3_code.append("              rw [he_mod] at this")\n    p3_code.append("              exact this.symm")\n    p3_code.append("            rw [h_div]")\n    p3_code.append("            decide")',
        '    p3_code.append("            have h_div : e = 112 * (e / 112) + 68 := by")\n    p3_code.append("              have := Nat.div_add_mod e 112")\n    p3_code.append("              rw [he_mod] at this")\n    p3_code.append("              exact this.symm")\n    p3_code.append("            rw [h_div]")\n    p3_code.append("            omega")'
    )

    # 7. Fix hq131
    content = content.replace(
        '    p3_code.append("          have h_zmod : (131 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")\n    p3_code.append("            have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("            have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")',
        '    p3_code.append("          have h_zmod : (131 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")\n    p3_code.append("            have h_ge : 131 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("            have h_cast : ((131 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")'
    )

    # 8. Fix hq167
    content = content.replace(
        '    p3_code.append("          have h_zmod : (167 : ZMod 83) ^ f - (3 : ZMod 83) ^ e = 2 := by")\n    p3_code.append("            have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("            have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 83) = ((2 : ℕ) : ZMod 83) := congrArg Nat.cast h")',
        '    p3_code.append("          have h_zmod : (167 : ZMod 83) ^ f - (3 : ZMod 83) ^ e = 2 := by")\n    p3_code.append("            have h_ge : 167 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("            have h_cast : ((167 ^ f - 3 ^ e : ℕ) : ZMod 83) = ((2 : ℕ) : ZMod 83) := congrArg Nat.cast h")'
    )
    content = content.replace(
        '    p3_code.append("          have h_cast2 : (3 : ZMod 83) ^ e = 82 := by")\n    p3_code.append("            calc (3 : ZMod 83) ^ e = - (- (3 : ZMod 83) ^ e) := by ring")\n    p3_code.append("            _ = -2 := by rw [h_zmod]")\n    p3_code.append("            _ = 82 := rfl")',
        '    p3_code.append("          have h_cast2 : (3 : ZMod 83) ^ e = 82 := by")\n    p3_code.append("            calc (3 : ZMod 83) ^ e = 1 - ((1 : ZMod 83) - (3 : ZMod 83) ^ e) := by ring")\n    p3_code.append("            _ = 1 - 2 := by rw [h_zmod]")\n    p3_code.append("            _ = 82 := rfl")'
    )

    # 9. Fix hq173
    content = content.replace(
        '    p3_code.append("            have h_zmod : (173 : ZMod 5) ^ f - (3 : ZMod 5) ^ e = 2 := by")\n    p3_code.append("              have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h")',
        '    p3_code.append("            have h_zmod : (173 : ZMod 5) ^ f - (3 : ZMod 5) ^ e = 2 := by")\n    p3_code.append("              have h_ge : 173 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h")'
    )
    content = content.replace(
        '    p3_code.append("              have h_zmod_local : (173 : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by")\n    p3_code.append("                have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("                have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h")',
        '    p3_code.append("              have h_zmod_local : (173 : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by")\n    p3_code.append("                have h_ge : 173 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("                have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h")'
    )

    # 10. Fix hq227
    content = content.replace(
        '    p3_code.append("            have h_zmod : (227 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")\n    p3_code.append("              have h_ge : q ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")',
        '    p3_code.append("            have h_zmod : (227 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")\n    p3_code.append("              have h_ge : 227 ^ f ≥ 3 ^ e := by omega")\n    p3_code.append("              have h_cast : ((227 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")'
    )

    with open("/workspace/leanproject/Submission/build_clean_spec.py", "w") as f:
        f.write(content)

    print("Substitutions applied successfully!")

if __name__ == "__main__":
    main()
