import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

def main():
    # Read the pristine head of Spec.lean
    with open("/workspace/leanproject/Submission/Spec_head.lean", "r") as f:
        spec_head = [line.rstrip("\r\n") for line in f.readlines()]
    
    primes = [p for p in range(3, 2000) if is_prime(p)]
    
    out = []
    out.extend(spec_head)
    out.append("\n-- Automatically generated modular helper lemmas\n")
    
    # 1. coprime_252_of_prime generator
    out.append("lemma coprime_252_of_prime (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :")
    out.append("    q % 252 ≠ 0 ∧ Nat.Coprime q 252 := by")
    out.append("  have h_gcd : q.gcd 252 = 1 := by")
    out.append("    by_contra hc")
    out.append("    have h_dvd : q.gcd 252 ∣ q := q.gcd_dvd_left 252")
    out.append("    have h_dvd2 : q.gcd 252 ∣ 252 := q.gcd_dvd_right 252")
    out.append("    rcases hq.eq_one_or_self_of_dvd _ h_dvd with h1 | h2")
    out.append("    · exact hc h1")
    out.append("    · have hq_dvd_252 : q ∣ 252 := h2 ▸ h_dvd2")
    out.append("      have hq252 : q ≤ 252 := Nat.le_of_dvd (by decide) hq_dvd_252")
    out.append("      interval_cases q")
    
    for q in range(253):
        if q == 0:
            out.append("      · exact (show ¬ Nat.Prime 0 by decide) hq")
        elif q == 1:
            out.append("      · exact (show ¬ Nat.Prime 1 by decide) hq")
        elif q == 2:
            out.append("      · exact hq2 rfl")
        elif q == 3:
            out.append("      · exact hq3 rfl")
        elif q == 7:
            out.append("      · exact hq7 rfl")
        else:
            is_prime_val = is_prime(q)
            if not is_prime_val:
                out.append(f"      · exact (show ¬ Nat.Prime {q} by decide) hq")
            else:
                out.append(f"      · exact (show ¬ {q} ∣ 252 by decide) hq_dvd_252")
                    
    out.append("  have h_mod : q % 252 ≠ 0 := by")
    out.append("    intro hc")
    out.append("    have : 252 ∣ q := Nat.dvd_of_mod_eq_zero hc")
    out.append("    have : q.gcd 252 = 252 := Nat.gcd_eq_right this")
    out.append("    omega")
    out.append("  exact ⟨h_mod, h_gcd⟩\n")

    # 2. pow_six_zmod_252 generator
    out.append("lemma pow_six_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) : (q : ZMod 252) ^ 6 = 1 := by")
    out.append("  set r := q % 252")
    out.append("  have hr_lt : r < 252 := Nat.mod_lt q (by decide)")
    out.append("  have q_mod : q % 252 = r := rfl")
    out.append("  interval_cases r")
    
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"  · exfalso")
            out.append(f"    have h_gcd_dvd : {g} ∣ q.gcd 252 := by")
            out.append(f"      have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"      have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"      have h_g_dvd_q : {g} ∣ q := by")
            out.append(f"        have : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
            out.append(f"        rw [this]")
            out.append(f"        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252")
            out.append(f"    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime")
            out.append(f"    rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"    have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"    revert this")
            out.append(f"    decide")
        else:
            out.append(f"  · have : (q : ZMod 252) = {r} := by")
            out.append(f"      have : q % 252 = {r} := q_mod")
            out.append(f"      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
            out.append(f"      rw [h_cast, this]")
            out.append(f"      rfl")
            out.append(f"    rw [this]")
            out.append(f"    decide")
    out.append("")

    # 3. pow_unit_zmod_252
    out.append("""lemma pow_unit_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) (f : ℕ) :
    (q : ZMod 252) ^ f = (q : ZMod 252) ^ (f % 6) := by
  have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul, pow_six_zmod_252 q hq_coprime, one_pow, one_mul]
""")

    # 4. pillai_diff_two_3_7 (mod 9)
    out.append("""lemma pillai_diff_two_3_7 (e f : ℕ) (he : 1 < e) (h : 7 ^ f - 3 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (7 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
    have h_ge : 7 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((7 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h3e : (3 : ZMod 9) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (3 : ZMod 9) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h3e, sub_zero] at h_zmod
  have h7f : (7 : ZMod 9) ^ f = (7 : ZMod 9) ^ (f % 3) := by
    have h_eq : f = 3 * (f / 3) + f % 3 := (Nat.div_add_mod f 3).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (7 : ZMod 9) ^ 3 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h7f] at h_zmod
  have h_mod : f % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 3 <;> revert h_zmod <;> decide
""")

    # 5. pillai_diff_two_5_7 (mod 25)
    out.append("""lemma pillai_diff_two_5_7 (e f : ℕ) (he : 1 < e) (h : 7 ^ f - 5 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (7 : ZMod 25) ^ f - (5 : ZMod 25) ^ e = 2 := by
    have h_ge : 7 ^ f ≥ 5 ^ e := by omega
    have h_cast : ((7 ^ f - 5 ^ e : ℕ) : ZMod 25) = ((2 : ℕ) : ZMod 25) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h5e : (5 : ZMod 25) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (5 : ZMod 25) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h5e, sub_zero] at h_zmod
  have h7f : (7 : ZMod 25) ^ f = (7 : ZMod 25) ^ (f % 4) := by
    have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (7 : ZMod 25) ^ 4 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h7f] at h_zmod
  have h_mod : f % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 4 <;> revert h_zmod <;> decide
""")

    # 6. pillai_diff_two_7_5 (mod 3)
    out.append("""lemma pillai_diff_two_7_5 (e f : ℕ) (h : 5 ^ f - 7 ^ e = 2) : False := by
  have h_zmod : (5 : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
    have h_ge : 5 ^ f ≥ 7 ^ e := by omega
    have h_cast : ((5 ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h5 : (5 : ZMod 3) = 2 := rfl
  have h7 : (7 : ZMod 3) = 1 := rfl
  rw [h5, h7, one_pow] at h_zmod
  have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
    have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul]
  rw [h2f] at h_zmod
  have h_mod : f % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 2 <;> revert h_zmod <;> decide
""")

    # 7. Mod 999 lemmas for pillai_diff_two_7_3
    out.append("""lemma pow_three_helper_999 (k : ℕ) : (3 : ZMod 999) ^ (18 * k + 3) = (3 : ZMod 999) ^ 3 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : 18 * (k + 1) + 3 = 18 * k + 3 + 18 := by omega
    rw [this, pow_add, ih]
    rfl

lemma pow_three_zmod_999 (f : ℕ) (hf : f ≥ 3) :
    (3 : ZMod 999) ^ f = (3 : ZMod 999) ^ ((f - 3) % 18 + 3) := by
  have h_eq : f = 18 * ((f - 3) / 18) + 3 + (f - 3) % 18 := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_three_helper_999, ← pow_add]
  have : 3 + (f - 3) % 18 = (f - 3) % 18 + 3 := by omega
  rw [this]

lemma pow_seven_zmod_999 (e : ℕ) (he : e ≥ 2) :
    (7 : ZMod 999) ^ e = (7 : ZMod 999) ^ ((e - 2) % 9 + 2) := by
  have h_eq : e = 9 * ((e - 2) / 9) + ((e - 2) % 9 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul]
  have : (7 : ZMod 999) ^ 9 = 1 := by rfl
  rw [this, one_pow, one_mul]

lemma pillai_diff_two_7_3 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 3 ^ f - 7 ^ e = 2) : False := by
  have hf3 : f ≥ 3 := by
    by_contra hc
    have : f = 2 := by omega
    subst this
    have : 3 ^ 2 - 7 ^ e = 2 := h
    have h_pow : 7 ^ e ≥ 49 := Nat.pow_le_pow_right (show 0 < 7 by decide) he
    omega
  have he2 : e ≥ 2 := he
  have h_zmod : (3 : ZMod 999) ^ f - (7 : ZMod 999) ^ e = 2 := by
    have h_ge : 3 ^ f ≥ 7 ^ e := by omega
    have h_cast : ((3 ^ f - 7 ^ e : ℕ) : ZMod 999) = ((2 : ℕ) : ZMod 999) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  rw [pow_three_zmod_999 f hf3, pow_seven_zmod_999 e he2] at h_zmod
  have h_mod_f : (f - 3) % 18 < 18 := Nat.mod_lt _ (by decide)
  have h_mod_e : (e - 2) % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : (f - 3) % 18 <;> interval_cases he_mod : (e - 2) % 9 <;> revert h_zmod <;> decide
""")

    # 8. Mod 121 lemmas for pillai_diff_two_3_11
    out.append("""lemma pillai_diff_two_3_11 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 11 ^ f - 3 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (11 : ZMod 121) ^ f - (3 : ZMod 121) ^ e = 2 := by
    have h_ge : 11 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((11 ^ f - 3 ^ e : ℕ) : ZMod 121) = ((2 : ℕ) : ZMod 121) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h11f : (11 : ZMod 121) ^ f = 0 := by
    have hf_eq : f = (f - 2) + 2 := by omega
    rw [hf_eq, pow_add]
    have : (11 : ZMod 121) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h11f, zero_sub] at h_zmod
  have h_cast2 : (3 : ZMod 121) ^ e = 119 := by
    calc (3 : ZMod 121) ^ e = - (- (3 : ZMod 121) ^ e) := by ring
    _ = -2 := by rw [h_zmod]
    _ = 119 := rfl
  have h3e : (3 : ZMod 121) ^ e = (3 : ZMod 121) ^ (e % 110) := by
    have h_eq : e = 110 * (e / 110) + e % 110 := (Nat.div_add_mod e 110).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 121) ^ 110 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h3e] at h_cast2
  have h_mod : e % 110 < 110 := Nat.mod_lt _ (by decide)
  interval_cases he_mod : e % 110 <;> revert h_cast2 <;> decide
""")

    # 9. Mod 252 helper for p = 7
    out.append("""lemma pow_seven_helper_252 (k : ℕ) : (7 : ZMod 252) ^ (6 * k + 2) = (7 : ZMod 252) ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : 6 * (k + 1) + 2 = 6 * k + 2 + 6 := by omega
    rw [this, pow_add, ih]
    rfl

lemma pow_seven_zmod_252 (e : ℕ) (he : e ≥ 2) :
    (7 : ZMod 252) ^ e = (7 : ZMod 252) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + 2 + (e - 2) % 6 := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_seven_helper_252, ← pow_add]
  have : 2 + (e - 2) % 6 = (e - 2) % 6 + 2 := by omega
  rw [this]
""")

    # 10. pillai_diff_two main lemma
    out.append("""lemma pillai_diff_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    p = 5 ∧ e = 2 ∧ q = 3 ∧ f = 3 := by
  by_cases hlt : p ^ e < 27
  · exact pillai_diff_two_lt_27 p q e f hp hq he hf h hlt
  · exfalso
    have hp_ne_2 : p ≠ 2 := p_ne_two p q e f hp hq he hf h
    have hq_ne_2 : q ≠ 2 := q_ne_two p q e f hp hq he hf h
    have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p ≥ 11 := by
      have : p ≠ 0 := hp.ne_zero
      have : p ≠ 1 := hp.ne_one
      have : p ≠ 4 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 6 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 8 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 9 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 10 := by intro hc; subst hc; revert hp; decide
      omega
    have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q ≥ 11 := by
      have : q ≠ 0 := hq.ne_zero
      have : q ≠ 1 := hq.ne_one
      have : q ≠ 4 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 6 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 8 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 9 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 10 := by intro hc; subst hc; revert hq; decide
      omega
    rcases hp_cases with rfl | rfl | rfl | rfl | hp_ge11
    · contradiction
    · -- p = 3
      have he3 : e ≥ 3 := by
        by_contra hc
        have : e = 2 := by omega
        subst this
        have : 3 ^ 2 < 27 := by decide
        omega
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · exact (q_ne_p_of_diff_two 3 3 e f hp he h rfl).elim
      · exact pillai_diff_two_3_5 e f (by omega) hf h
      · exact pillai_diff_two_3_7 e f (by omega) h
      · by_cases hq11 : q = 11
        · subst hq11
          exact pillai_diff_two_3_11 e f (by omega) hf h
        · have hq_ge13 : q ≥ 13 := by omega
          -- use ZMod 252
          have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2
          have h_zmod : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by
            have h_ge : q ^ f ≥ 3 ^ e := by omega
            have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          rw [pow_unit_zmod_252 q hq_coprime f, pow_three_zmod_252 e (by omega)] at h_zmod
          set r := q % 252
          have hr_lt : r < 252 := Nat.mod_lt q (by decide)
          have q_mod : q % 252 = r := rfl
          interval_cases r""")
          
    # Now we output the cases of interval_cases r for p = 3, q >= 13
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"          · exfalso")
            out.append(f"            have h_gcd_dvd : {g} ∣ q.gcd 252 := by")
            out.append(f"              have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"              have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"              have h_g_dvd_q : {g} ∣ q := by")
            out.append(f"                have : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
            out.append(f"                rw [this]")
            out.append(f"                exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"              exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252")
            out.append(f"            have h_gcd_1 : q.gcd 252 = 1 := hq_coprime")
            out.append(f"            rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"            have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"            revert this")
            out.append(f"            decide")
        else:
            if r in [1, 5]:
                out.append(f"          · exfalso")
                out.append(f"            have : q = {r} := by")
                out.append(f"              have : q % 252 = {r} := q_mod")
                out.append(f"              omega")
                out.append(f"            omega")
                continue
            has_sol = False
            for f_val in range(2, 8):
                for e_val in range(3, 9):
                    if (pow(r, f_val, 252) - pow(3, e_val, 252) - 2) % 252 == 0:
                        has_sol = True
                        break
            if not has_sol:
                out.append(f"          · have : (q : ZMod 252) = {r} := by")
                out.append(f"              have : q % 252 = {r} := q_mod")
                out.append(f"              have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                out.append(f"              rw [h_cast, this]")
                out.append(f"              rfl")
                out.append(f"            rw [this] at h_zmod")
                out.append(f"            have h_mod_f : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"            have h_mod_e : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"            interval_cases hf_mod : f % 6 <;> interval_cases he_mod : (e - 2) % 6 <;> revert h_zmod <;> decide")
            else:
                prime_mod = None
                for M_cand in [p for p in primes if p != 3]:
                    if math.gcd(r, M_cand) != 1:
                        continue
                    seen3 = {}
                    ev = 3
                    while True:
                        val = pow(3, ev, M_cand)
                        if val in seen3:
                            start3 = seen3[val]
                            period3 = ev - seen3[val]
                            break
                        seen3[val] = ev
                        ev += 1
                    seen_q = {}
                    fv = 2
                    while True:
                        val = pow(r, fv, M_cand)
                        if val in seen_q:
                            start_q = seen_q[val]
                            period_q = fv - seen_q[val]
                            break
                        seen_q[val] = fv
                        fv += 1
                    has_sol_M = False
                    for ev_val in range(3, start3 + period3):
                        for fv_val in range(2, start_q + period_q):
                            if (pow(r, fv_val, M_cand) - pow(3, ev_val, M_cand) - 2) % M_cand == 0:
                                has_sol_M = True
                                break
                        if has_sol_M:
                            break
                    if not has_sol_M:
                        prime_mod = M_cand
                        break
                if prime_mod is not None:
                    phi = prime_mod - 1
                    out.append(f"          · -- Modulo {prime_mod} rules out r = {r}")
                    out.append(f"            have h_zmod_new : ({r} : ZMod {prime_mod}) ^ f - (3 : ZMod {prime_mod}) ^ e = 2 := by")
                    out.append(f"              have : q % 252 = {r} := q_mod")
                    out.append(f"              have h_eq_q : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    out.append(f"              have h_div : {prime_mod} ∣ 252 := by decide")
                    out.append(f"              have h_eq_q_new : q % {prime_mod} = {r % prime_mod} := by")
                    out.append(f"                rw [h_eq_q]")
                    out.append(f"                have : 252 * (q / 252) % {prime_mod} = 0 := by")
                    out.append(f"                  rcases h_div with ⟨c, hc⟩")
                    out.append(f"                  use c * (q / 252)")
                    out.append(f"                  rw [hc]")
                    out.append(f"                  ring")
                    out.append(f"                omega")
                    out.append(f"              have h_cast_q : ((q : ℕ) : ZMod {prime_mod}) = {r % prime_mod} := by")
                    out.append(f"                have : ((q : ℕ) : ZMod {prime_mod}) = ((q % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                    out.append(f"                rw [this, h_eq_q_new]")
                    out.append(f"                rfl")
                    out.append(f"              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                    out.append(f"              have h_ge : q ^ f ≥ 3 ^ e := by omega")
                    out.append(f"              rw [Nat.cast_sub h_ge] at h_cast")
                    out.append(f"              push_cast at h_cast")
                    out.append(f"              rw [h_cast_q] at h_cast")
                    out.append(f"              exact h_cast")
                    out.append(f"            have h_pow_q : ({r % prime_mod} : ZMod {prime_mod}) ^ f = ({r % prime_mod} : ZMod {prime_mod}) ^ (f % {phi}) := by")
                    out.append(f"              have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                    out.append(f"              conv_lhs => rw [h_eq]")
                    out.append(f"              rw [pow_add, pow_mul]")
                    out.append(f"              have : ({r % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"              rw [this, one_pow, one_mul]")
                    out.append(f"            have h_pow_3 : (3 : ZMod {prime_mod}) ^ e = (3 : ZMod {prime_mod}) ^ (e % {phi}) := by")
                    out.append(f"              have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                    out.append(f"              conv_lhs => rw [h_eq]")
                    out.append(f"              rw [pow_add, pow_mul]")
                    out.append(f"              have : (3 : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"              rw [this, one_pow, one_mul]")
                    out.append(f"            rw [h_pow_q, h_pow_3] at h_zmod_new")
                    out.append(f"            have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"            have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"            interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                else:
                    print(f"Error: No prime modulus found for r = {r}")

    # Remaining cases for p = 5, 7, >= 11
    out.append("""    · -- p = 5
      have he3 : e ≥ 3 := by
        by_contra hc
        have : e = 2 := by omega
        subst this
        have : 5 ^ 2 < 27 := by decide
        omega
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1
        omega
      · exact (q_ne_p_of_diff_two 5 5 e f hp he h rfl).elim
      · exact pillai_diff_two_5_7 e f he h
      · -- p = 5, q >= 11
        have hp_coprime : Nat.Coprime 5 252 := by decide
        have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2
        have h_zmod : (q : ZMod 252) ^ f - (5 : ZMod 252) ^ e = 2 := by
          have h_ge : q ^ f ≥ 5 ^ e := by omega
          have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        rw [pow_unit_zmod_252 q hq_coprime f, pow_unit_zmod_252 5 hp_coprime e] at h_zmod
        set r := q % 252
        have hr_lt : r < 252 := Nat.mod_lt q (by decide)
        have q_mod : q % 252 = r := rfl
        interval_cases r""")
        
    # We output the interval_cases r for p = 5, q >= 11
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"        · exfalso")
            out.append(f"          have h_gcd_dvd : {g} ∣ q.gcd 252 := by")
            out.append(f"            have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"            have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"            have h_g_dvd_q : {g} ∣ q := by")
            out.append(f"              have : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
            out.append(f"              rw [this]")
            out.append(f"              exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"            exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252")
            out.append(f"          have h_gcd_1 : q.gcd 252 = 1 := hq_coprime")
            out.append(f"          rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"          have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"          revert this")
            out.append(f"          decide")
        else:
            if r in [1, 5]:
                out.append(f"        · exfalso")
                out.append(f"          have : q = {r} := by")
                out.append(f"            have : q % 252 = {r} := q_mod")
                out.append(f"            omega")
                out.append(f"          omega")
                continue
            has_sol = False
            for f_val in range(2, 8):
                for e_val in range(2, 8):
                    if (pow(r, f_val, 252) - pow(5, e_val, 252) - 2) % 252 == 0:
                        has_sol = True
                        break
            if not has_sol:
                out.append(f"        · have : (q : ZMod 252) = {r} := by")
                out.append(f"            have : q % 252 = {r} := q_mod")
                out.append(f"            have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                out.append(f"            rw [h_cast, this]")
                out.append(f"            rfl")
                out.append(f"          rw [this] at h_zmod")
                out.append(f"          have h_mod_f : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          have h_mod_e : e % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          interval_cases hf_mod : f % 6 <;> interval_cases he_mod : e % 6 <;> revert h_zmod <;> decide")
            else:
                prime_mod = None
                for M_cand in [p for p in primes if p != 5]:
                    if math.gcd(r, M_cand) != 1:
                        continue
                    seen5 = {}
                    ev = 2
                    while True:
                        val = pow(5, ev, M_cand)
                        if val in seen5:
                            start5 = seen5[val]
                            period5 = ev - seen5[val]
                            break
                        seen5[val] = ev
                        ev += 1
                    seen_q = {}
                    fv = 2
                    while True:
                        val = pow(r, fv, M_cand)
                        if val in seen_q:
                            start_q = seen_q[val]
                            period_q = fv - seen_q[val]
                            break
                        seen_q[val] = fv
                        fv += 1
                    has_sol_M = False
                    for ev_val in range(2, start5 + period5):
                        for fv_val in range(2, start_q + period_q):
                            if (pow(r, fv_val, M_cand) - pow(5, ev_val, M_cand) - 2) % M_cand == 0:
                                has_sol_M = True
                                break
                        if has_sol_M:
                            break
                    if not has_sol_M:
                        prime_mod = M_cand
                        break
                if prime_mod is not None:
                    phi = prime_mod - 1
                    out.append(f"        · -- Modulo {prime_mod} rules out r = {r}")
                    out.append(f"          have h_zmod_new : ({r} : ZMod {prime_mod}) ^ f - (5 : ZMod {prime_mod}) ^ e = 2 := by")
                    out.append(f"            have : q % 252 = {r} := q_mod")
                    out.append(f"            have h_eq_q : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    out.append(f"            have h_div : {prime_mod} ∣ 252 := by decide")
                    out.append(f"            have h_eq_q_new : q % {prime_mod} = {r % prime_mod} := by")
                    out.append(f"              rw [h_eq_q]")
                    out.append(f"              have : 252 * (q / 252) % {prime_mod} = 0 := by")
                    out.append(f"                rcases h_div with ⟨c, hc⟩")
                    out.append(f"                use c * (q / 252)")
                    out.append(f"                rw [hc]")
                    out.append(f"                ring")
                    out.append(f"              omega")
                    out.append(f"            have h_cast_q : ((q : ℕ) : ZMod {prime_mod}) = {r % prime_mod} := by")
                    out.append(f"                have : ((q : ℕ) : ZMod {prime_mod}) = ((q % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                    out.append(f"                rw [this, h_eq_q_new]")
                    out.append(f"                rfl")
                    out.append(f"            have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                    out.append(f"            have h_ge : q ^ f ≥ 5 ^ e := by omega")
                    out.append(f"            rw [Nat.cast_sub h_ge] at h_cast")
                    out.append(f"            push_cast at h_cast")
                    out.append(f"            rw [h_cast_q] at h_cast")
                    out.append(f"            exact h_cast")
                    out.append(f"          have h_pow_q : ({r % prime_mod} : ZMod {prime_mod}) ^ f = ({r % prime_mod} : ZMod {prime_mod}) ^ (f % {phi}) := by")
                    out.append(f"            have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : ({r % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          have h_pow_5 : (5 : ZMod {prime_mod}) ^ e = (5 : ZMod {prime_mod}) ^ (e % {phi}) := by")
                    out.append(f"            have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : (5 : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          rw [h_pow_q, h_pow_5] at h_zmod_new")
                    out.append(f"          have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                else:
                    print(f"Error: No prime modulus found for p = 5, r = {r}")

    # 11. Remaining cases: p = 7
    out.append("""    · -- p = 7
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · exact pillai_diff_two_7_3 e f he hf h
      · exact pillai_diff_two_7_5 e f h
      · exact (q_ne_p_of_diff_two 7 7 e f hp he h rfl).elim
      · -- p = 7, q >= 11
        have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2
        have h_zmod : (q : ZMod 252) ^ f - (7 : ZMod 252) ^ e = 2 := by
          have h_ge : q ^ f ≥ 7 ^ e := by omega
          have h_cast : ((q ^ f - 7 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        rw [pow_unit_zmod_252 q hq_coprime f, pow_seven_zmod_252 e (by omega)] at h_zmod
        set r := q % 252
        have hr_lt : r < 252 := Nat.mod_lt q (by decide)
        have q_mod : q % 252 = r := rfl
        interval_cases r""")
        
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"        · exfalso")
            out.append(f"          have h_gcd_dvd : {g} ∣ q.gcd 252 := by")
            out.append(f"            have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"            have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"            have h_g_dvd_q : {g} ∣ q := by")
            out.append(f"              have : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
            out.append(f"              rw [this]")
            out.append(f"              exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"            exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252")
            out.append(f"          have h_gcd_1 : q.gcd 252 = 1 := hq_coprime")
            out.append(f"          rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"          have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"          revert this")
            out.append(f"          decide")
        else:
            if r in [1, 5]:
                out.append(f"        · exfalso")
                out.append(f"          have : q = {r} := by")
                out.append(f"            have : q % 252 = {r} := q_mod")
                out.append(f"            omega")
                out.append(f"          omega")
                continue
            has_sol = False
            for f_val in range(2, 8):
                for e_val in range(2, 8):
                    if (pow(r, f_val, 252) - pow(7, e_val, 252) - 2) % 252 == 0:
                        has_sol = True
                        break
            if not has_sol:
                out.append(f"        · have : (q : ZMod 252) = {r} := by")
                out.append(f"            have : q % 252 = {r} := q_mod")
                out.append(f"            have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                out.append(f"            rw [h_cast, this]")
                out.append(f"            rfl")
                out.append(f"          rw [this] at h_zmod")
                out.append(f"          have h_mod_f : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          have h_mod_e : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          interval_cases hf_mod : f % 6 <;> interval_cases he_mod : (e - 2) % 6 <;> revert h_zmod <;> decide")
            else:
                prime_mod = None
                for M_cand in [p for p in primes if p != 7]:
                    if math.gcd(r, M_cand) != 1:
                        continue
                    seen7 = {}
                    ev = 2
                    while True:
                        val = pow(7, ev, M_cand)
                        if val in seen7:
                            start7 = seen7[val]
                            period7 = ev - seen7[val]
                            break
                        seen7[val] = ev
                        ev += 1
                    seen_q = {}
                    fv = 2
                    while True:
                        val = pow(r, fv, M_cand)
                        if val in seen_q:
                            start_q = seen_q[val]
                            period_q = fv - seen_q[val]
                            break
                        seen_q[val] = fv
                        fv += 1
                    has_sol_M = False
                    for ev_val in range(2, start7 + period7):
                        for fv_val in range(2, start_q + period_q):
                            if (pow(r, fv_val, M_cand) - pow(7, ev_val, M_cand) - 2) % M_cand == 0:
                                has_sol_M = True
                                break
                        if has_sol_M:
                            break
                    if not has_sol_M:
                        prime_mod = M_cand
                        break
                if prime_mod is not None:
                    phi = prime_mod - 1
                    out.append(f"        · -- Modulo {prime_mod} rules out r = {r}")
                    out.append(f"          have h_zmod_new : ({r} : ZMod {prime_mod}) ^ f - (7 : ZMod {prime_mod}) ^ e = 2 := by")
                    out.append(f"            have : q % 252 = {r} := q_mod")
                    out.append(f"            have h_eq_q : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    out.append(f"            have h_div : {prime_mod} ∣ 252 := by decide")
                    out.append(f"            have h_eq_q_new : q % {prime_mod} = {r % prime_mod} := by")
                    out.append(f"              rw [h_eq_q]")
                    out.append(f"              have : 252 * (q / 252) % {prime_mod} = 0 := by")
                    out.append(f"                rcases h_div with ⟨c, hc⟩")
                    out.append(f"                use c * (q / 252)")
                    out.append(f"                rw [hc]")
                    out.append(f"                ring")
                    out.append(f"              omega")
                    out.append(f"            have h_cast_q : ((q : ℕ) : ZMod {prime_mod}) = {r % prime_mod} := by")
                    out.append(f"                have : ((q : ℕ) : ZMod {prime_mod}) = ((q % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                    out.append(f"                rw [this, h_eq_q_new]")
                    out.append(f"                rfl")
                    out.append(f"            have h_cast : ((q ^ f - 7 ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                    out.append(f"            have h_ge : q ^ f ≥ 7 ^ e := by omega")
                    out.append(f"            rw [Nat.cast_sub h_ge] at h_cast")
                    out.append(f"            push_cast at h_cast")
                    out.append(f"            rw [h_cast_q] at h_cast")
                    out.append(f"            exact h_cast")
                    out.append(f"          have h_pow_q : ({r % prime_mod} : ZMod {prime_mod}) ^ f = ({r % prime_mod} : ZMod {prime_mod}) ^ (f % {phi}) := by")
                    out.append(f"            have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : ({r % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          have h_pow_7 : (7 : ZMod {prime_mod}) ^ e = (7 : ZMod {prime_mod}) ^ (e % {phi}) := by")
                    out.append(f"            have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : (7 : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          rw [h_pow_q, h_pow_7] at h_zmod_new")
                    out.append(f"          have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                else:
                    print(f"Error: No prime modulus found for p = 7, r = {r}")

    # 12. Remaining cases: p >= 11
    out.append("""    · -- p >= 11
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · -- q = 3
        have hp_coprime : Nat.Coprime p 252 := (coprime_252_of_prime p hp hp_ne_2 (by omega) (by omega)).2
        have h_zmod : (3 : ZMod 252) ^ f - (p : ZMod 252) ^ e = 2 := by
          have h_ge : 3 ^ f ≥ p ^ e := by omega
          have h_cast : ((3 ^ f - p ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        rw [pow_three_zmod_252 f (by omega), pow_unit_zmod_252 p hp_coprime e] at h_zmod
        set r := p % 252
        have hr_lt : r < 252 := Nat.mod_lt p (by decide)
        have p_mod : p % 252 = r := rfl
        interval_cases r""")
        
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"        · exfalso")
            out.append(f"          have h_gcd_dvd : {g} ∣ p.gcd 252 := by")
            out.append(f"            have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"            have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"            have h_g_dvd_p : {g} ∣ p := by")
            out.append(f"              have : p = 252 * (p / 252) + {r} := (Nat.div_add_mod p 252).symm.trans (by omega)")
            out.append(f"              rw [this]")
            out.append(f"              exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"            exact Nat.dvd_gcd h_g_dvd_p h_g_dvd_252")
            out.append(f"          have h_gcd_1 : p.gcd 252 = 1 := hp_coprime")
            out.append(f"          rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"          have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"          revert this")
            out.append(f"          decide")
        else:
            if r in [1, 5]:
                out.append(f"        · exfalso")
                out.append(f"          have : p = {r} := by")
                out.append(f"            have : p % 252 = {r} := p_mod")
                out.append(f"            omega")
                out.append(f"          omega")
                continue
            has_sol = False
            for f_val in range(2, 8):
                for e_val in range(2, 8):
                    if (pow(3, f_val, 252) - pow(r, e_val, 252) - 2) % 252 == 0:
                        has_sol = True
                        break
            if not has_sol:
                out.append(f"        · have : (p : ZMod 252) = {r} := by")
                out.append(f"            have : p % 252 = {r} := p_mod")
                out.append(f"            have h_cast : ((p : ℕ) : ZMod 252) = ((p % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                out.append(f"            rw [h_cast, this]")
                out.append(f"            rfl")
                out.append(f"          rw [this] at h_zmod")
                out.append(f"          have h_mod_f : (f - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          have h_mod_e : e % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          interval_cases hf_mod : (f - 2) % 6 <;> interval_cases he_mod : e % 6 <;> revert h_zmod <;> decide")
            else:
                prime_mod = None
                for M_cand in [p for p in primes if p != 3]:
                    if math.gcd(r, M_cand) != 1:
                        continue
                    seen3 = {}
                    fv = 2
                    while True:
                        val = pow(3, fv, M_cand)
                        if val in seen3:
                            start3 = seen3[val]
                            period3 = fv - seen3[val]
                            break
                        seen3[val] = fv
                        fv += 1
                    seen_p = {}
                    ev = 2
                    while True:
                        val = pow(r, ev, M_cand)
                        if val in seen_p:
                            start_p = seen_p[val]
                            period_p = ev - seen_p[val]
                            break
                        seen_p[val] = ev
                        ev += 1
                    has_sol_M = False
                    for fv_val in range(2, start3 + period3):
                        for ev_val in range(2, start_p + period_p):
                            if (pow(3, fv_val, M_cand) - pow(r, ev_val, M_cand) - 2) % M_cand == 0:
                                has_sol_M = True
                                break
                        if has_sol_M:
                            break
                    if not has_sol_M:
                        prime_mod = M_cand
                        break
                if prime_mod is not None:
                    phi = prime_mod - 1
                    out.append(f"        · -- Modulo {prime_mod} rules out r = {r}")
                    out.append(f"          have h_zmod_new : (3 : ZMod {prime_mod}) ^ f - ({r} : ZMod {prime_mod}) ^ e = 2 := by")
                    out.append(f"            have : p % 252 = {r} := p_mod")
                    out.append(f"            have h_eq_p : p = 252 * (p / 252) + {r} := (Nat.div_add_mod p 252).symm.trans (by omega)")
                    out.append(f"            have h_div : {prime_mod} ∣ 252 := by decide")
                    out.append(f"            have h_eq_p_new : p % {prime_mod} = {r % prime_mod} := by")
                    out.append(f"              rw [h_eq_p]")
                    out.append(f"              have : 252 * (p / 252) % {prime_mod} = 0 := by")
                    out.append(f"                rcases h_div with ⟨c, hc⟩")
                    out.append(f"                use c * (p / 252)")
                    out.append(f"                rw [hc]")
                    out.append(f"                ring")
                    out.append(f"              omega")
                    out.append(f"            have h_cast_p : ((p : ℕ) : ZMod {prime_mod}) = {r % prime_mod} := by")
                    out.append(f"                have : ((p : ℕ) : ZMod {prime_mod}) = ((p % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                    out.append(f"                rw [this, h_eq_p_new]")
                    out.append(f"                rfl")
                    out.append(f"            have h_cast : ((3 ^ f - p ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                    out.append(f"            have h_ge : 3 ^ f ≥ p ^ e := by omega")
                    out.append(f"            rw [Nat.cast_sub h_ge] at h_cast")
                    out.append(f"            push_cast at h_cast")
                    out.append(f"            rw [h_cast_p] at h_cast")
                    out.append(f"            exact h_cast")
                    out.append(f"          have h_pow_3 : (3 : ZMod {prime_mod}) ^ f = (3 : ZMod {prime_mod}) ^ (f % {phi}) := by")
                    out.append(f"            have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : (3 : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          have h_pow_p : ({r % prime_mod} : ZMod {prime_mod}) ^ e = ({r % prime_mod} : ZMod {prime_mod}) ^ (e % {phi}) := by")
                    out.append(f"            have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : ({r % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          rw [h_pow_3, h_pow_p] at h_zmod_new")
                    out.append(f"          have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                else:
                    print(f"Error: No prime modulus found for q = 3, r = {r}")

    # remaining: p >= 11, q = 5
    out.append("""      · -- q = 5
        have hp_coprime : Nat.Coprime p 252 := (coprime_252_of_prime p hp hp_ne_2 (by omega) (by omega)).2
        have h_zmod : (5 : ZMod 252) ^ f - (p : ZMod 252) ^ e = 2 := by
          have h_ge : 5 ^ f ≥ p ^ e := by omega
          have h_cast : ((5 ^ f - p ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        rw [pow_five_zmod_252 f, pow_unit_zmod_252 p hp_coprime e] at h_zmod
        set r := p % 252
        have hr_lt : r < 252 := Nat.mod_lt p (by decide)
        have p_mod : p % 252 = r := rfl
        interval_cases r""")
        
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"        · exfalso")
            out.append(f"          have h_gcd_dvd : {g} ∣ p.gcd 252 := by")
            out.append(f"            have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"            have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"            have h_g_dvd_p : {g} ∣ p := by")
            out.append(f"              have : p = 252 * (p / 252) + {r} := (Nat.div_add_mod p 252).symm.trans (by omega)")
            out.append(f"              rw [this]")
            out.append(f"              exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"            exact Nat.dvd_gcd h_g_dvd_p h_g_dvd_252")
            out.append(f"          have h_gcd_1 : p.gcd 252 = 1 := hp_coprime")
            out.append(f"          rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"          have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"          revert this")
            out.append(f"          decide")
        else:
            if r in [1, 5]:
                out.append(f"        · exfalso")
                out.append(f"          have : p = {r} := by")
                out.append(f"            have : p % 252 = {r} := p_mod")
                out.append(f"            omega")
                out.append(f"          omega")
                continue
            has_sol = False
            for f_val in range(2, 8):
                for e_val in range(2, 8):
                    if (pow(5, f_val, 252) - pow(r, e_val, 252) - 2) % 252 == 0:
                        has_sol = True
                        break
            if not has_sol:
                out.append(f"        · have : (p : ZMod 252) = {r} := by")
                out.append(f"            have : p % 252 = {r} := p_mod")
                out.append(f"            have h_cast : ((p : ℕ) : ZMod 252) = ((p % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                out.append(f"            rw [h_cast, this]")
                out.append(f"            rfl")
                out.append(f"          rw [this] at h_zmod")
                out.append(f"          have h_mod_f : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          have h_mod_e : e % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          interval_cases hf_mod : f % 6 <;> interval_cases he_mod : e % 6 <;> revert h_zmod <;> decide")
            else:
                prime_mod = None
                for M_cand in [p for p in primes if p != 5]:
                    if math.gcd(r, M_cand) != 1:
                        continue
                    seen5 = {}
                    fv = 2
                    while True:
                        val = pow(5, fv, M_cand)
                        if val in seen5:
                            start5 = seen5[val]
                            period5 = fv - seen5[val]
                            break
                        seen5[val] = fv
                        fv += 1
                    seen_p = {}
                    ev = 2
                    while True:
                        val = pow(r, ev, M_cand)
                        if val in seen_p:
                            start_p = seen_p[val]
                            period_p = ev - seen_p[val]
                            break
                        seen_p[val] = ev
                        ev += 1
                    has_sol_M = False
                    for fv_val in range(2, start5 + period5):
                        for ev_val in range(2, start_p + period_p):
                            if (pow(5, fv_val, M_cand) - pow(r, ev_val, M_cand) - 2) % M_cand == 0:
                                has_sol_M = True
                                break
                        if has_sol_M:
                            break
                    if not has_sol_M:
                        prime_mod = M_cand
                        break
                if prime_mod is not None:
                    phi = prime_mod - 1
                    out.append(f"        · -- Modulo {prime_mod} rules out r = {r}")
                    out.append(f"          have h_zmod_new : (5 : ZMod {prime_mod}) ^ f - ({r} : ZMod {prime_mod}) ^ e = 2 := by")
                    out.append(f"            have : p % 252 = {r} := p_mod")
                    out.append(f"            have h_eq_p : p = 252 * (p / 252) + {r} := (Nat.div_add_mod p 252).symm.trans (by omega)")
                    out.append(f"            have h_div : {prime_mod} ∣ 252 := by decide")
                    out.append(f"            have h_eq_p_new : p % {prime_mod} = {r % prime_mod} := by")
                    out.append(f"              rw [h_eq_p]")
                    out.append(f"              have : 252 * (p / 252) % {prime_mod} = 0 := by")
                    out.append(f"                rcases h_div with ⟨c, hc⟩")
                    out.append(f"                use c * (p / 252)")
                    out.append(f"                rw [hc]")
                    out.append(f"                ring")
                    out.append(f"              omega")
                    out.append(f"            have h_cast_p : ((p : ℕ) : ZMod {prime_mod}) = {r % prime_mod} := by")
                    out.append(f"                have : ((p : ℕ) : ZMod {prime_mod}) = ((p % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                    out.append(f"                rw [this, h_eq_p_new]")
                    out.append(f"                rfl")
                    out.append(f"            have h_cast : ((5 ^ f - p ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                    out.append(f"            have h_ge : 5 ^ f ≥ p ^ e := by omega")
                    out.append(f"            rw [Nat.cast_sub h_ge] at h_cast")
                    out.append(f"            push_cast at h_cast")
                    out.append(f"            rw [h_cast_p] at h_cast")
                    out.append(f"            exact h_cast")
                    out.append(f"          have h_pow_5 : (5 : ZMod {prime_mod}) ^ f = (5 : ZMod {prime_mod}) ^ (f % {phi}) := by")
                    out.append(f"            have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : (5 : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          have h_pow_p : ({r % prime_mod} : ZMod {prime_mod}) ^ e = ({r % prime_mod} : ZMod {prime_mod}) ^ (e % {phi}) := by")
                    out.append(f"            have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : ({r % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          rw [h_pow_5, h_pow_p] at h_zmod_new")
                    out.append(f"          have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                else:
                    print(f"Error: No prime modulus found for p = 5, r = {r}")

    # remaining: p >= 11, q = 7
    out.append("""      · -- q = 7
        have hp_coprime : Nat.Coprime p 252 := (coprime_252_of_prime p hp hp_ne_2 (by omega) (by omega)).2
        have h_zmod : (7 : ZMod 252) ^ f - (p : ZMod 252) ^ e = 2 := by
          have h_ge : 7 ^ f ≥ p ^ e := by omega
          have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        rw [pow_seven_zmod_252 f (by omega), pow_unit_zmod_252 p hp_coprime e] at h_zmod
        set r := p % 252
        have hr_lt : r < 252 := Nat.mod_lt p (by decide)
        have p_mod : p % 252 = r := rfl
        interval_cases r""")
        
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            out.append(f"        · exfalso")
            out.append(f"          have h_gcd_dvd : {g} ∣ p.gcd 252 := by")
            out.append(f"            have h_g_dvd_252 : {g} ∣ 252 := by decide")
            out.append(f"            have h_g_dvd_r : {g} ∣ {r} := by decide")
            out.append(f"            have h_g_dvd_p : {g} ∣ p := by")
            out.append(f"              have : p = 252 * (p / 252) + {r} := (Nat.div_add_mod p 252).symm.trans (by omega)")
            out.append(f"              rw [this]")
            out.append(f"              exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"            exact Nat.dvd_gcd h_g_dvd_p h_g_dvd_252")
            out.append(f"          have h_gcd_1 : p.gcd 252 = 1 := hp_coprime")
            out.append(f"          rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"          have : {g} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"          revert this")
            out.append(f"          decide")
        else:
            if r in [1, 5]:
                out.append(f"        · exfalso")
                out.append(f"          have : p = {r} := by")
                out.append(f"            have : p % 252 = {r} := p_mod")
                out.append(f"            omega")
                out.append(f"          omega")
                continue
            has_sol = False
            for f_val in range(2, 8):
                for e_val in range(2, 8):
                    if (pow(7, f_val, 252) - pow(r, e_val, 252) - 2) % 252 == 0:
                        has_sol = True
                        break
            if not has_sol:
                out.append(f"        · have : (p : ZMod 252) = {r} := by")
                out.append(f"            have : p % 252 = {r} := p_mod")
                out.append(f"            have h_cast : ((p : ℕ) : ZMod 252) = ((p % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                out.append(f"            rw [h_cast, this]")
                out.append(f"            rfl")
                out.append(f"          rw [this] at h_zmod")
                out.append(f"          have h_mod_f : (f - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          have h_mod_e : e % 6 < 6 := Nat.mod_lt _ (by decide)")
                out.append(f"          interval_cases hf_mod : (f - 2) % 6 <;> interval_cases he_mod : e % 6 <;> revert h_zmod <;> decide")
            else:
                prime_mod = None
                for M_cand in [p for p in primes if p != 7]:
                    if math.gcd(r, M_cand) != 1:
                        continue
                    seen7 = {}
                    fv = 2
                    while True:
                        val = pow(7, fv, M_cand)
                        if val in seen7:
                            start7 = seen7[val]
                            period7 = fv - seen7[val]
                            break
                        seen7[val] = fv
                        fv += 1
                    seen_p = {}
                    ev = 2
                    while True:
                        val = pow(r, ev, M_cand)
                        if val in seen_p:
                            start_p = seen_p[val]
                            period_p = ev - seen_p[val]
                            break
                        seen_p[val] = ev
                        ev += 1
                    has_sol_M = False
                    for fv_val in range(2, start7 + period7):
                        for ev_val in range(2, start_p + period_p):
                            if (pow(7, fv_val, M_cand) - pow(r, ev_val, M_cand) - 2) % M_cand == 0:
                                has_sol_M = True
                                break
                        if has_sol_M:
                            break
                    if not has_sol_M:
                        prime_mod = M_cand
                        break
                if prime_mod is not None:
                    phi = prime_mod - 1
                    out.append(f"        · -- Modulo {prime_mod} rules out r = {r}")
                    out.append(f"          have h_zmod_new : (7 : ZMod {prime_mod}) ^ f - ({r} : ZMod {prime_mod}) ^ e = 2 := by")
                    out.append(f"            have : p % 252 = {r} := p_mod")
                    out.append(f"            have h_eq_p : p = 252 * (p / 252) + {r} := (Nat.div_add_mod p 252).symm.trans (by omega)")
                    out.append(f"            have h_div : {prime_mod} ∣ 252 := by decide")
                    out.append(f"            have h_eq_p_new : p % {prime_mod} = {r % prime_mod} := by")
                    out.append(f"              rw [h_eq_p]")
                    out.append(f"              have : 252 * (p / 252) % {prime_mod} = 0 := by")
                    out.append(f"                rcases h_div with ⟨c, hc⟩")
                    out.append(f"                use c * (p / 252)")
                    out.append(f"                rw [hc]")
                    out.append(f"                ring")
                    out.append(f"              omega")
                    out.append(f"            have h_cast_p : ((p : ℕ) : ZMod {prime_mod}) = {r % prime_mod} := by")
                    out.append(f"                have : ((p : ℕ) : ZMod {prime_mod}) = ((p % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                    out.append(f"                rw [this, h_eq_p_new]")
                    out.append(f"                rfl")
                    out.append(f"            have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                    out.append(f"            have h_ge : 7 ^ f ≥ p ^ e := by omega")
                    out.append(f"            rw [Nat.cast_sub h_ge] at h_cast")
                    out.append(f"            push_cast at h_cast")
                    out.append(f"            rw [h_cast_p] at h_cast")
                    out.append(f"            exact h_cast")
                    out.append(f"          have h_pow_7 : (7 : ZMod {prime_mod}) ^ f = (7 : ZMod {prime_mod}) ^ (f % {phi}) := by")
                    out.append(f"            have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : (7 : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          have h_pow_p : ({r % prime_mod} : ZMod {prime_mod}) ^ e = ({r % prime_mod} : ZMod {prime_mod}) ^ (e % {phi}) := by")
                    out.append(f"            have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                    out.append(f"            conv_lhs => rw [h_eq]")
                    out.append(f"            rw [pow_add, pow_mul]")
                    out.append(f"            have : ({r % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                    out.append(f"            rw [this, one_pow, one_mul]")
                    out.append(f"          rw [h_pow_7, h_pow_p] at h_zmod_new")
                    out.append(f"          have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                    out.append(f"          interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                else:
                    print(f"Error: No prime modulus found for q = 7, r = {r}")

    # remaining: p >= 11, q >= 11 (contradiction by Mod 252)
    out.append("""      · -- q >= 11
        have hp_coprime : Nat.Coprime p 252 := (coprime_252_of_prime p hp hp_ne_2 (by omega) (by omega)).2
        have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2
        have h_zmod : (q : ZMod 252) ^ f - (p : ZMod 252) ^ e = 2 := by
          have h_ge : q ^ f ≥ p ^ e := by omega
          have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        rw [pow_unit_zmod_252 q hq_coprime f, pow_unit_zmod_252 p hp_coprime e] at h_zmod
        set rp := p % 252
        have hrp_lt : rp < 252 := Nat.mod_lt p (by decide)
        have p_mod : p % 252 = rp := rfl
        set rq := q % 252
        have hrq_lt : rq < 252 := Nat.mod_lt q (by decide)
        have q_mod : q % 252 = rq := rfl
        interval_cases rp""")
        
    for rp in range(252):
        g_p = math.gcd(rp, 252)
        if g_p > 1:
            out.append(f"        · exfalso")
            out.append(f"          have h_gcd_dvd : {g_p} ∣ p.gcd 252 := by")
            out.append(f"            have h_g_dvd_252 : {g_p} ∣ 252 := by decide")
            out.append(f"            have h_g_dvd_r : {g_p} ∣ {rp} := by decide")
            out.append(f"            have h_g_dvd_p : {g_p} ∣ p := by")
            out.append(f"              have : p = 252 * (p / 252) + {rp} := (Nat.div_add_mod p 252).symm.trans (by omega)")
            out.append(f"              rw [this]")
            out.append(f"              exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
            out.append(f"            exact Nat.dvd_gcd h_g_dvd_p h_g_dvd_252")
            out.append(f"          have h_gcd_1 : p.gcd 252 = 1 := hp_coprime")
            out.append(f"          rw [h_gcd_1] at h_gcd_dvd")
            out.append(f"          have : {g_p} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
            out.append(f"          revert this")
            out.append(f"          decide")
        else:
            if rp in [1, 5]:
                out.append(f"        · exfalso")
                out.append(f"          have : p = {rp} := by")
                out.append(f"            have : p % 252 = {rp} := p_mod")
                out.append(f"            omega")
                out.append(f"          omega")
                continue
            out.append(f"        · interval_cases rq")
            for rq in range(252):
                g_q = math.gcd(rq, 252)
                if g_q > 1:
                    out.append(f"          · exfalso")
                    out.append(f"            have h_gcd_dvd : {g_q} ∣ q.gcd 252 := by")
                    out.append(f"              have h_g_dvd_252 : {g_q} ∣ 252 := by decide")
                    out.append(f"              have h_g_dvd_r : {g_q} ∣ {rq} := by decide")
                    out.append(f"              have h_g_dvd_q : {g_q} ∣ q := by")
                    out.append(f"                have : q = 252 * (q / 252) + {rq} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    out.append(f"                rw [this]")
                    out.append(f"                exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r")
                    out.append(f"              exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252")
                    out.append(f"            have h_gcd_1 : q.gcd 252 = 1 := hq_coprime")
                    out.append(f"            rw [h_gcd_1] at h_gcd_dvd")
                    out.append(f"            have : {g_q} ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd")
                    out.append(f"            revert this")
                    out.append(f"            decide")
                else:
                    if rq in [1, 5]:
                        out.append(f"          · exfalso")
                        out.append(f"            have : q = {rq} := by")
                        out.append(f"              have : q % 252 = {rq} := q_mod")
                        out.append(f"              omega")
                        out.append(f"            omega")
                        continue
                    has_sol = False
                    for f_val in range(2, 8):
                        for e_val in range(2, 8):
                            if (pow(rq, f_val, 252) - pow(rp, e_val, 252) - 2) % 252 == 0:
                                has_sol = True
                                break
                    if not has_sol:
                        out.append(f"          · have hp_cast : (p : ZMod 252) = {rp} := by")
                        out.append(f"              have : p % 252 = {rp} := p_mod")
                        out.append(f"              have h_cast : ((p : ℕ) : ZMod 252) = ((p % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                        out.append(f"              rw [h_cast, this]")
                        out.append(f"              rfl")
                        out.append(f"            have hq_cast : (q : ZMod 252) = {rq} := by")
                        out.append(f"              have : q % 252 = {rq} := q_mod")
                        out.append(f"              have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                        out.append(f"              rw [h_cast, this]")
                        out.append(f"              rfl")
                        out.append(f"            rw [hp_cast, hq_cast] at h_zmod")
                        out.append(f"            have h_mod_f : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                        out.append(f"            have h_mod_e : e % 6 < 6 := Nat.mod_lt _ (by decide)")
                        out.append(f"            interval_cases hf_mod : f % 6 <;> interval_cases he_mod : e % 6 <;> revert h_zmod <;> decide")
                    else:
                        prime_mod = None
                        for M_cand in [p for p in primes]:
                            if math.gcd(rp, M_cand) != 1 or math.gcd(rq, M_cand) != 1:
                                continue
                            seen_p = {}
                            ev = 2
                            while True:
                                val = pow(rp, ev, M_cand)
                                if val in seen_p:
                                    start_p = seen_p[val]
                                    period_p = ev - seen_p[val]
                                    break
                                seen_p[val] = ev
                                ev += 1
                            seen_q = {}
                            fv = 2
                            while True:
                                val = pow(rq, fv, M_cand)
                                if val in seen_q:
                                    start_q = seen_q[val]
                                    period_q = fv - seen_q[val]
                                    break
                                seen_q[val] = fv
                                fv += 1
                            has_sol_M = False
                            for fv_val in range(2, start_q + period_q):
                                for ev_val in range(2, start_p + period_p):
                                    if (pow(rq, fv_val, M_cand) - pow(rp, ev_val, M_cand) - 2) % M_cand == 0:
                                        has_sol_M = True
                                        break
                                if has_sol_M:
                                    break
                            if not has_sol_M:
                                prime_mod = M_cand
                                break
                        if prime_mod is not None:
                            phi = prime_mod - 1
                            out.append(f"          · -- Modulo {prime_mod} rules out rp = {rp}, rq = {rq}")
                            out.append(f"            have h_zmod_new : ({rq} : ZMod {prime_mod}) ^ f - ({rp} : ZMod {prime_mod}) ^ e = 2 := by")
                            out.append(f"              have hp_eq : p = 252 * (p / 252) + {rp} := (Nat.div_add_mod p 252).symm.trans (by omega)")
                            out.append(f"              have hq_eq : q = 252 * (q / 252) + {rq} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                            out.append(f"              have h_div : {prime_mod} ∣ 252 := by decide")
                            out.append(f"              have h_eq_p_new : p % {prime_mod} = {rp % prime_mod} := by")
                            out.append(f"                rw [hp_eq]")
                            out.append(f"                have : 252 * (p / 252) % {prime_mod} = 0 := by")
                            out.append(f"                  rcases h_div with ⟨c, hc⟩")
                            out.append(f"                  use c * (p / 252)")
                            out.append(f"                  rw [hc]")
                            out.append(f"                  ring")
                            out.append(f"                omega")
                            out.append(f"              have h_eq_q_new : q % {prime_mod} = {rq % prime_mod} := by")
                            out.append(f"                rw [hq_eq]")
                            out.append(f"                have : 252 * (q / 252) % {prime_mod} = 0 := by")
                            out.append(f"                  rcases h_div with ⟨c, hc⟩")
                            out.append(f"                  use c * (q / 252)")
                            out.append(f"                  rw [hc]")
                            out.append(f"                  ring")
                            out.append(f"                omega")
                            out.append(f"              have h_cast_p : ((p : ℕ) : ZMod {prime_mod}) = {rp % prime_mod} := by")
                            out.append(f"                have : ((p : ℕ) : ZMod {prime_mod}) = ((p % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                            out.append(f"                rw [this, h_eq_p_new]")
                            out.append(f"                rfl")
                            out.append(f"              have h_cast_q : ((q : ℕ) : ZMod {prime_mod}) = {rq % prime_mod} := by")
                            out.append(f"                have : ((q : ℕ) : ZMod {prime_mod}) = ((q % {prime_mod} : ℕ) : ZMod {prime_mod}) := by rw [ZMod.natCast_mod]")
                            out.append(f"                rw [this, h_eq_q_new]")
                            out.append(f"                rfl")
                            out.append(f"              have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod {prime_mod}) = ((2 : ℕ) : ZMod {prime_mod}) := congrArg Nat.cast h")
                            out.append(f"              have h_ge : q ^ f ≥ p ^ e := by omega")
                            out.append(f"              rw [Nat.cast_sub h_ge] at h_cast")
                            out.append(f"              push_cast at h_cast")
                            out.append(f"              rw [h_cast_q, h_cast_p] at h_cast")
                            out.append(f"              exact h_cast")
                            out.append(f"            have h_pow_q : ({rq % prime_mod} : ZMod {prime_mod}) ^ f = ({rq % prime_mod} : ZMod {prime_mod}) ^ (f % {phi}) := by")
                            out.append(f"              have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                            out.append(f"              conv_lhs => rw [h_eq]")
                            out.append(f"              rw [pow_add, pow_mul]")
                            out.append(f"              have : ({rq % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                            out.append(f"              rw [this, one_pow, one_mul]")
                            out.append(f"            have h_pow_p : ({rp % prime_mod} : ZMod {prime_mod}) ^ e = ({rp % prime_mod} : ZMod {prime_mod}) ^ (e % {phi}) := by")
                            out.append(f"              have h_eq : e = {phi} * (e / {phi}) + e % {phi} := (Nat.div_add_mod e {phi}).symm")
                            out.append(f"              conv_lhs => rw [h_eq]")
                            out.append(f"              rw [pow_add, pow_mul]")
                            out.append(f"              have : ({rp % prime_mod} : ZMod {prime_mod}) ^ {phi} = 1 := by decide")
                            out.append(f"              rw [this, one_pow, one_mul]")
                            out.append(f"            rw [h_pow_q, h_pow_p] at h_zmod_new")
                            out.append(f"            have h_mod_f : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                            out.append(f"            have h_mod_e : e % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                            out.append(f"            interval_cases hf_mod : f % {phi} <;> interval_cases he_mod : e % {phi} <;> revert h_zmod_new <;> decide")
                        else:
                            print(f"Error: No prime modulus found for rp = {rp}, rq = {rq}")

    # Append the main conjecture oeis_365416_conjecture_0
    out.append("\ntheorem oeis_365416_conjecture_0 :")
    out.append("  ∀ k : ℕ,")
    out.append("    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by")
    out.append("  intro k")
    out.append("  constructor")
    out.append("  · intro h")
    out.append("    by_cases hk13 : k = 13")
    out.append("    · exact hk13")
    out.append("    · exfalso")
    out.append("      by_cases hk_lt : k < 14")
    out.append("      · interval_cases k")
    out.append("        · exact not_isCompositePrimePow_of_lt_four 0 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_lt_four 1 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_lt_four 3 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 5 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 7 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 11 (by decide) h.2")
    out.append("        · exact not_isCompositePrimePow_of_prime 11 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 13 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 17 (by decide) h.2")
    out.append("        · exact not_isCompositePrimePow_of_prime 17 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 19 (by decide) h.1")
    out.append("        · exact not_isCompositePrimePow_of_prime 23 (by decide) h.2")
    out.append("        · exact not_isCompositePrimePow_of_prime 23 (by decide) h.1")
    out.append("        · exact hk13 rfl")
    out.append("      · have h_ge : k ≥ 14 := by omega")
    out.append("        rcases h with ⟨h1, h2⟩")
    out.append("        rcases h1 with ⟨p, e, hp, he, hp_eq⟩")
    out.append("        rcases h2 with ⟨q, f, hq, hf, hq_eq⟩")
    out.append("        have h_sub : q ^ f - p ^ e = 2 := by")
    out.append("          omega")
    out.append("        have h_pillai := pillai_diff_two p q e f hp hq he f h_sub")
    out.append("        have hp_eq5 : p = 5 := h_pillai.1")
    out.append("        have he_eq2 : e = 2 := h_pillai.2.1")
    out.append("        have : 2 * k - 1 = 25 := by")
    out.append("          calc 2 * k - 1 = p ^ e := hp_eq.symm")
    out.append("          _ = 5 ^ 2 := by rw [hp_eq5, he_eq2]")
    out.append("          _ = 25 := by rfl")
    out.append("        omega")
    out.append("  · intro h")
    out.append("    subst h")
    out.append("    constructor")
    out.append("    · use 5, 2")
    out.append("      refine ⟨by decide, by decide, by rfl⟩")
    out.append("    · use 3, 3")
    out.append("      refine ⟨by decide, by decide, by rfl⟩")
    out.append("\n\n#print axioms oeis_365416_conjecture_0")
    
    with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
        f.write("\n".join(out) + "\n")

if __name__ == "__main__":
    main()
