import math

def generate_pow_six():
    out = []
    out.append("import FormalConjectures.Util.ProblemImports")
    out.append("set_option maxRecDepth 1000000")
    out.append("\nopen Nat\n")
    out.append("lemma pow_six_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) : (q : ZMod 252) ^ 6 = 1 := by")
    out.append("  set r := q % 252")
    out.append("  have hr_lt : r < 252 := Nat.mod_lt q (by decide)")
    out.append("  have q_mod : q % 252 = r := rfl")
    out.append("  interval_cases r")
    
    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            # Not coprime branch
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
            # Coprime branch
            out.append(f"  · have : (q : ZMod 252) = {r} := by")
            out.append(f"      have : q % 252 = {r} := q_mod")
            out.append(f"      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
            out.append(f"      rw [h_cast, this]")
            out.append(f"      rfl")
            out.append(f"    rw [this]")
            out.append(f"    decide")

    with open("/workspace/leanproject/Submission/pow_six.lean", "w") as f:
        f.write("\n".join(out) + "\n")

if __name__ == "__main__":
    generate_pow_six()
