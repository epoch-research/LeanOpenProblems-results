import sys

# Read the fast greedy output
with open("Submission/greedy_fast_out.txt") as f:
    lines = f.readlines()

n0_str = None
used_primes_str = None
blocked_str = None

for line in lines:
    if "SUCCESS!" in line:
        pass
    if line.startswith("n0 ="):
        n0_str = line.split("=")[1].strip()
    elif line.startswith("used_primes ="):
        used_primes_str = line.split("=")[1].strip()
    elif line.startswith("blocked ="):
        blocked_str = line.split("=")[1].strip()

if not n0_str:
    print("Not succeeded yet!")
    sys.exit(0)

n0 = int(n0_str)
used_primes = eval(used_primes_str)
blocked = eval(blocked_str)

# Generate get_V_all
def get_V_all(limit):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

V_all = get_V_all(n0*n0)
primes_check = [3, 7] + [p for p, _ in used_primes]

v_to_prime = {}
for v in V_all:
    val = n0*n0 - v
    found = False
    for p in primes_check:
        if val % p == 0 and val % (p*p) != 0:
            v_to_prime[v] = p
            found = True
            break
    if not found:
        print(f"Error: v = {v} is not blocked by any prime!")
        sys.exit(1)

# Split V_all into chunks of size 500
chunk_size = 500
chunks = [V_all[i:i + chunk_size] for i in range(0, len(V_all), chunk_size)]

# We will generate Spec.lean
out_lines = [
    "/-",
    "Copyright 2026 The Formal Conjectures Authors.",
    "-/",
    "import FormalConjectures.Util.ProblemImports",
    "",
    "set_option linter.style.namespace false",
    "",
    "open Nat Finset Int",
    "",
    "def a (n : ℕ) : ℕ :=",
    "  let R := Finset.range (n + 1)",
    "  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)",
    "",
    "  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>",
    "    let x := p.fst.fst; let y := p.fst.snd;",
    "    let z := p.snd.fst; let w := p.snd.snd;",
    "",
    "    x^2 + y^2 + z^2 + w^2 = n^2 ∧",
    "    z ≤ w ∧",
    "    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))",
    "  )",
    "",
    "lemma not_sq_add_sq (m : ℕ) (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) (h1 : p ∣ m) (h2 : ¬ p^2 ∣ m) :",
    "    ¬ ∃ z w : ℕ, z^2 + w^2 = m := by",
    "  intro ⟨z, w, hzw⟩",
    "  have hm0 : m ≠ 0 := by",
    "    rintro rfl",
    "    apply h2",
    "    exact dvd_zero (p^2)",
    "  have h_padic : padicValNat p m = 1 := by",
    "    have h_le : 1 ≤ padicValNat p m := one_le_padicValNat_of_dvd hm0 h1",
    "    have h_lt : padicValNat p m < 2 := by",
    "      by_contra h_ge",
    "      push_neg at h_ge",
    "      have h_pow_dvd : p^2 ∣ m := (padicValNat_dvd_iff_le hm0).mpr h_ge",
    "      contradiction",
    "    omega",
    "  have h_eq : (∃ x y, m = x ^ 2 + y ^ 2) := ⟨z, w, hzw.symm⟩",
    "  rw [Nat.eq_sq_add_sq_iff] at h_eq",
    "  have hp_mem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.out, h1, hm0⟩",
    "  have h_even : Even (padicValNat p m) := h_eq p hp_mem hp3",
    "  rw [h_padic] at h_even",
    "  contradiction",
    "",
    "lemma classification_step (x y k : ℕ) (h_eq : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) :",
    "    ∃ u v : ℕ, u + v = 2 * k ∧ 36 * (x^2 + y^2) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by",
    "  have h_4k : (4^k : ℤ) ≥ 0 := by positivity",
    "  have h_ge_int : (x^2 : ℤ) ≥ (3 * y : ℤ)^2 := by",
    "    omega",
    "  have h_ge_nat : (3 * y)^2 ≤ x^2 := by",
    "    exact_mod_cast h_ge_int",
    "  have h_ge : 3 * y ≤ x := by",
    "    rwa [Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)] at h_ge_nat",
    "  have h_sub_cast : ((x - 3 * y : ℕ) : ℤ) = (x : ℤ) - (3 * y : ℤ) := Int.ofNat_sub h_ge",
    "  have h_add_cast : ((x + 3 * y : ℕ) : ℤ) = (x : ℤ) + (3 * y : ℤ) := by push_cast; rfl",
    "  have h_ge' : (x^2 : ℕ) ≥ (3 * y)^2 := h_ge_nat",
    "  have h_prod_int : ((x - 3 * y : ℕ) : ℤ) * ((x + 3 * y : ℕ) : ℤ) = (x^2 : ℤ) - (3 * y : ℤ)^2 := by",
    "    rw [h_sub_cast, h_add_cast]",
    "    ring",
    "  have h_4k_eq : 4^k = 2^(2 * k) := by",
    "    rw [show 4 = 2^2 by rfl, ← Nat.pow_mul]",
    "  have h_prod_nat : (x - 3 * y) * (x + 3 * y) = 2^(2 * k) := by",
    "    have h_prod_cast : (((x - 3 * y) * (x + 3 * y) : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) := by",
    "      rw [Nat.cast_mul]",
    "      rw [h_prod_int, h_eq]",
    "      rw [show (4^k : ℤ) = ((4^k : ℕ) : ℤ) by rfl]",
    "      rw [show ((4^k : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) by rw [h_4k_eq]]",
    "    exact_mod_cast h_prod_cast",
    "  have h_dvd_left : (x - 3 * y) ∣ 2^(2 * k) := ⟨x + 3 * y, h_prod_nat.symm⟩",
    "  have h_dvd_right : (x + 3 * y) ∣ 2^(2 * k) := by",
    "    use (x - 3 * y)",
    "    rw [mul_comm (x + 3 * y)]",
    "    exact h_prod_nat.symm",
    "  obtain ⟨u, hu_le, hu_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_left",
    "  obtain ⟨v, hv_le, hv_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_right",
    "  have h_pow_sum : 2^(u + v) = 2^(2 * k) := by",
    "    rw [pow_add, ← hu_eq, ← hv_eq, h_prod_nat]",
    "  have h_uv : u + v = 2 * k := Nat.pow_right_injective (by decide) h_pow_sum",
    "  use u, v",
    "  refine ⟨h_uv, ?_⟩",
    "  have h_id_int : (36 * (x^2 + y^2) : ℤ) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by",
    "    have hA : (2^u : ℤ) = (x : ℤ) - (3 * y : ℤ) := by",
    "      exact_mod_cast hu_eq.symm",
    "    have hB : (2^v : ℤ) = (x : ℤ) + (3 * y : ℤ) := by",
    "      exact_mod_cast hv_eq.symm",
    "    have h_v2 : (2^(2*v) : ℤ) = (2^v : ℤ)^2 := by",
    "      rw [← pow_mul, mul_comm]",
    "    have h_u2 : (2^(2*u) : ℤ) = (2^u : ℤ)^2 := by",
    "      rw [← pow_mul, mul_comm]",
    "    have h_2k : (2^(2*k) : ℤ) = (2^u : ℤ) * (2^v : ℤ) := by",
    "      rw [← pow_add, ← h_uv]",
    "    rw [h_v2, h_u2, h_2k, hA, hB]",
    "    ring",
    "  exact_mod_cast h_id_int",
    "",
    f"def N : ℕ := {n0}",
    ""
]

# Generate chunk functions
for chunk_idx, chunk in enumerate(chunks):
    out_lines.append(f"def blocking_prime_{chunk_idx} (v : ℕ) : ℕ :=")
    out_lines.append("  match v with")
    for v in chunk:
        p = v_to_prime[v]
        out_lines.append(f"  | {v} => {p}")
    out_lines.append("  | _ => 3")
    out_lines.append("")
    out_lines.append(f"lemma blocking_prime_{chunk_idx}_prime (v : ℕ) : Nat.Prime (blocking_prime_{chunk_idx} v) :=")
    out_lines.append(f"  by unfold blocking_prime_{chunk_idx}; split <;> decide")
    out_lines.append("")
    out_lines.append(f"lemma blocking_prime_{chunk_idx}_3mod4 (v : ℕ) : blocking_prime_{chunk_idx} v % 4 = 3 :=")
    out_lines.append(f"  by unfold blocking_prime_{chunk_idx}; split <;> decide")
    out_lines.append("")

# Now, the main blocking_prime function
blocking_prime_lines = [
    "def blocking_prime (v : ℕ) : ℕ :="
]
for chunk_idx, chunk in enumerate(chunks[:-1]):
    boundary = chunks[chunk_idx+1][0]
    blocking_prime_lines.append(f"  if v < {boundary} then blocking_prime_{chunk_idx} v")
    blocking_prime_lines.append("  else")
blocking_prime_lines.append(f"    blocking_prime_{len(chunks)-1} v")
blocking_prime_lines.append("")
out_lines.extend(blocking_prime_lines)

# Proof of primality for main blocking_prime
blocking_prime_prime_lines = [
    "lemma blocking_prime_prime (v : ℕ) : Nat.Prime (blocking_prime v) :=",
    "  by",
    "    unfold blocking_prime"
]
for chunk_idx, chunk in enumerate(chunks[:-1]):
    blocking_prime_prime_lines.append("    split")
    blocking_prime_prime_lines.append(f"    · exact blocking_prime_{chunk_idx}_prime v")
blocking_prime_prime_lines.append(f"    exact blocking_prime_{len(chunks)-1}_prime v")
blocking_prime_prime_lines.append("")
out_lines.extend(blocking_prime_prime_lines)

# Proof of 3 mod 4 for main blocking_prime
blocking_prime_3mod4_lines = [
    "lemma blocking_prime_3mod4 (v : ℕ) : blocking_prime v % 4 = 3 :=",
    "  by",
    "    unfold blocking_prime"
]
for chunk_idx, chunk in enumerate(chunks[:-1]):
    blocking_prime_3mod4_lines.append("    split")
    blocking_prime_3mod4_lines.append(f"    · exact blocking_prime_{chunk_idx}_3mod4 v")
blocking_prime_3mod4_lines.append(f"    exact blocking_prime_{len(chunks)-1}_3mod4 v")
blocking_prime_3mod4_lines.append("")
out_lines.extend(blocking_prime_3mod4_lines)

# Generate is_blocked
out_lines.append("def is_blocked (v : ℕ) : Bool :=")
out_lines.append("  let p := blocking_prime v")
out_lines.append("  (N^2 - v) % p == 0 && (N^2 - v) % (p^2) != 0")
out_lines.append("")

# Generate is_blocked theorems
out_lines.append("theorem is_blocked_all : ∀ s < 40, ∀ i < 160, is_blocked (4^i * (10 * 16^s + 16 * 4^s + 10) / 9) = true := by decide")
out_lines.append("theorem is_blocked_one : is_blocked 1 = true := by decide")
out_lines.append("")

# Generate main disproof
out_lines.append("theorem A301376_conjecture.disproof : ¬ ∀ (n : ℕ), n > 0 → a n > 0 := by")
out_lines.append("  intro h")
out_lines.append("  have h_pos : N > 0 := by decide")
out_lines.append("  have h_a := h N h_pos")
out_lines.append("  unfold a at h_a")
out_lines.append("  rw [Finset.card_pos, Finset.filter_nonempty_iff] at h_a")
out_lines.append("  obtain ⟨p, hp⟩ := h_a")
out_lines.append("  rw [Finset.mem_filter] at hp")
out_lines.append("  rcases hp with ⟨h_dom, h_sum, h_zw, k, hk_mem, hk_eq⟩")
out_lines.append("  obtain ⟨u, v_pow, h_uv, h_eq_class⟩ := classification_step p.1.1 p.1.2 k hk_eq")
out_lines.append("  have h_cases : u = 0 ∨ u ≥ 1 := by omega")
out_lines.append("  rcases h_cases with rfl | hu_ge")
out_lines.append("  · -- Case u = 0")
out_lines.append("    have h_k_cases : k = 0 ∨ k ≥ 1 := by omega")
out_lines.append("    rcases h_k_cases with rfl | hk_ge")
out_lines.append("    · -- Subcase k = 0")
out_lines.append("      have h_v0 : v_pow = 0 := by omega")
out_lines.append("      subst h_v0")
out_lines.append("      have h_sum_class : 36 * (p.1.1^2 + p.1.2^2) = 36 := by")
                    # using h_eq_class and arithmetic
out_lines.append("        rw [h_eq_class]")
out_lines.append("        rfl")
out_lines.append("      have h_v_one : p.1.1^2 + p.1.2^2 = 1 := by omega")
out_lines.append("      have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - 1 := by")
out_lines.append("        use p.2.1, p.2.2")
out_lines.append("        omega")
out_lines.append("      have h_blocked_one : is_blocked 1 = true := is_blocked_one")
out_lines.append("      unfold is_blocked at h_blocked_one")
out_lines.append("      have h_p_prop : (N^2 - 1) % (blocking_prime 1) = 0 ∧ (N^2 - 1) % (blocking_prime 1)^2 ≠ 0 := by")
out_lines.append("        revert h_blocked_one")
out_lines.append("        decide")
out_lines.append("      have h_prime_fact : Fact (Nat.Prime (blocking_prime 1)) := ⟨blocking_prime_prime 1⟩")
out_lines.append("      have h_prime_3mod4 : blocking_prime 1 % 4 = 3 := blocking_prime_3mod4 1")
out_lines.append("      have h_dvd : blocking_prime 1 ∣ N^2 - 1 := Nat.dvd_of_mod_eq_zero h_p_prop.1")
out_lines.append("      have h_not_dvd : ¬ (blocking_prime 1)^2 ∣ N^2 - 1 := by")
out_lines.append("        intro hd")
out_lines.append("        have h_mod : (N^2 - 1) % (blocking_prime 1)^2 = 0 := Nat.mod_eq_zero_of_dvd hd")
out_lines.append("        exact h_p_prop.2 h_mod")
out_lines.append("      have h_no_rep := not_sq_add_sq (N^2 - 1) (blocking_prime 1) h_prime_3mod4 h_dvd h_not_dvd")
out_lines.append("      exact h_no_rep h_two_sq")
out_lines.append("    · -- Subcase k >= 1")
out_lines.append("      have h_v_eq : v_pow = 2 * k := by omega")
out_lines.append("      rw [h_v_eq] at h_eq_class")
out_lines.append("      have h_rhs_mod : (10 * 2^(2 * (2 * k)) + 16 * 2^(2 * k) + 10 * 2^(2 * 0)) % 4 = 2 := by")
out_lines.append("        -- Since k >= 1, 2 * k >= 2, so 2^(4k) and 2^(2k) are multiples of 4")
out_lines.append("        -- 10 * 2^(4k) is multiple of 4, 16 * 2^(2k) is multiple of 4")
out_lines.append("        -- 10 * 2^0 = 10, 10 % 4 = 2")
out_lines.append("        have h_k_ge : 2 * k ≥ 2 := by omega")
out_lines.append("        have h_pow1 : 4 ∣ 2^(2 * (2 * k)) := by")
out_lines.append("          use 2^(2 * (2 * k) - 2)")
out_lines.append("          have : 2 * (2 * k) = (2 * (2 * k) - 2) + 2 := by omega")
out_lines.append("          rw [this, pow_add]")
out_lines.append("          rfl")
out_lines.append("        have h_pow2 : 4 ∣ 2^(2 * k) := by")
out_lines.append("          use 2^(2 * k - 2)")
out_lines.append("          have : 2 * k = (2 * k - 2) + 2 := by omega")
out_lines.append("          rw [this, pow_add]")
out_lines.append("          rfl")
out_lines.append("        omega")
out_lines.append("      have h_lhs_mod : (36 * (p.1.1^2 + p.1.2^2)) % 4 = 0 := by")
out_lines.append("        use 9 * (p.1.1^2 + p.1.2^2)")
out_lines.append("        ring")
out_lines.append("      omega")
out_lines.append("  · -- Case u >= 1")
out_lines.append("    let i := u - 1")
out_lines.append("    let s := k - u")
out_lines.append("    have h_s_bounds : s < 40 := by")
out_lines.append("      by_contra hc")
out_lines.append("      push_neg at hc")
out_lines.append("      have h_pow16 : 10 * 16^s ≥ 10 * 16^40 := by")
out_lines.append("        gcongr")
out_lines.append("        decide")
out_lines.append("      have h_val_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ 10 * 16^40 / 9 := by")
out_lines.append("        have : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 10 * 16^s := by")
out_lines.append("          have : 4^i ≥ 1 := by positivity")
out_lines.append("          nlinarith")
out_lines.append("        omega")
out_lines.append("      have h_v_bound : p.1.1^2 + p.1.2^2 ≥ N^2 := by")
                    # using h_eq_class, s and i definitions
out_lines.append("        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := by")
out_lines.append("          have h_id_int' : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (4 * 4^i * (10 * 16^s + 16 * 4^s + 10) : ℤ) := by")
out_lines.append("            rw [h_eq_class]")
out_lines.append("            have h1 : 2^(2 * v_pow) = 2^(2 * (u + s + s)) := by")
out_lines.append("              have : v_pow = u + 2 * s := by omega")
out_lines.append("              rw [this]")
out_lines.append("              rfl")
out_lines.append("            have h2 : 2^(2 * k) = 2^(2 * (u + s)) := by")
out_lines.append("              have : k = u + s := by omega")
out_lines.append("              rw [this]")
out_lines.append("              rfl")
out_lines.append("            push_cast")
out_lines.append("            ring")
out_lines.append("          have h_id_nat : 36 * (p.1.1^2 + p.1.2^2) = 4 * 4^i * (10 * 16^s + 16 * 4^s + 10) := by")
out_lines.append("            exact_mod_cast h_id_int'")
out_lines.append("          omega")
out_lines.append("        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by")
out_lines.append("          rw [← h_eq_class']")
out_lines.append("          rw [Nat.mul_div_cancel_left]")
out_lines.append("          decide")
out_lines.append("        rw [h_div]")
out_lines.append("        omega")
out_lines.append("      omega")
out_lines.append("    have h_i_bounds : i < 160 := by")
out_lines.append("      by_contra hc")
out_lines.append("      push_neg at hc")
out_lines.append("      have h_pow4 : 4^i ≥ 4^160 := by")
out_lines.append("        gcongr")
out_lines.append("        decide")
out_lines.append("      have h_v_bound : p.1.1^2 + p.1.2^2 ≥ N^2 := by")
out_lines.append("        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := by")
out_lines.append("          have h_id_int' : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (4 * 4^i * (10 * 16^s + 16 * 4^s + 10) : ℤ) := by")
out_lines.append("            rw [h_eq_class]")
out_lines.append("            have h1 : 2^(2 * v_pow) = 2^(2 * (u + s + s)) := by")
out_lines.append("              have : v_pow = u + 2 * s := by omega")
out_lines.append("              rw [this]")
out_lines.append("              rfl")
out_lines.append("            have h2 : 2^(2 * k) = 2^(2 * (u + s)) := by")
out_lines.append("              have : k = u + s := by omega")
out_lines.append("              rw [this]")
out_lines.append("              rfl")
out_lines.append("            push_cast")
out_lines.append("            ring")
out_lines.append("          have h_id_nat : 36 * (p.1.1^2 + p.1.2^2) = 4 * 4^i * (10 * 16^s + 16 * 4^s + 10) := by")
out_lines.append("            exact_mod_cast h_id_int'")
out_lines.append("          omega")
out_lines.append("        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by")
out_lines.append("          rw [← h_eq_class']")
out_lines.append("          rw [Nat.mul_div_cancel_left]")
out_lines.append("          decide")
out_lines.append("        rw [h_div]")
out_lines.append("        omega")
out_lines.append("      omega")
out_lines.append("    have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := by")
out_lines.append("      have h_id_int' : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (4 * 4^i * (10 * 16^s + 16 * 4^s + 10) : ℤ) := by")
out_lines.append("        rw [h_eq_class]")
out_lines.append("        have h1 : 2^(2 * v_pow) = 2^(2 * (u + s + s)) := by")
out_lines.append("          have : v_pow = u + 2 * s := by omega")
out_lines.append("          rw [this]")
out_lines.append("          rfl")
out_lines.append("        have h2 : 2^(2 * k) = 2^(2 * (u + s)) := by")
out_lines.append("          have : k = u + s := by omega")
out_lines.append("          rw [this]")
out_lines.append("          rfl")
out_lines.append("        push_cast")
out_lines.append("        ring")
out_lines.append("      have h_id_nat : 36 * (p.1.1^2 + p.1.2^2) = 4 * 4^i * (10 * 16^s + 16 * 4^s + 10) := by")
out_lines.append("        exact_mod_cast h_id_int'")
out_lines.append("      omega")
out_lines.append("    have h_v_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by")
out_lines.append("      rw [← h_eq_class']")
out_lines.append("      rw [Nat.mul_div_cancel_left]")
out_lines.append("      decide")
out_lines.append("    have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - (p.1.1^2 + p.1.2^2) := by")
out_lines.append("      use p.2.1, p.2.2")
out_lines.append("      omega")
out_lines.append("    have h_blocked : is_blocked (4^i * (10 * 16^s + 16 * 4^s + 10) / 9) = true := is_blocked_all s h_s_bounds i h_i_bounds")
out_lines.append("    rw [← h_v_div] at h_blocked")
out_lines.append("    let p' := blocking_prime (p.1.1^2 + p.1.2^2)")
out_lines.append("    unfold is_blocked at h_blocked")
out_lines.append("    have h_p_prop : (N^2 - (p.1.1^2 + p.1.2^2)) % p' = 0 ∧ (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 ≠ 0 := by")
out_lines.append("      revert h_blocked")
out_lines.append("      decide")
out_lines.append("    have h_prime_fact : Fact (Nat.Prime p') := by")
out_lines.append("      have : Nat.Prime p' := by")
out_lines.append("        -- Since p' is the result of blocking_prime, it must be prime. Bounded check is fast.")
out_lines.append("        revert h_blocked")
out_lines.append("        decide")
out_lines.append("      exact ⟨this⟩")
out_lines.append("    have h_prime_3mod4 : p' % 4 = 3 := by")
out_lines.append("      revert h_blocked")
out_lines.append("      decide")
out_lines.append("    have h_dvd : p' ∣ N^2 - (p.1.1^2 + p.1.2^2) := Nat.dvd_of_mod_eq_zero h_p_prop.1")
out_lines.append("    have h_not_dvd : ¬ p'^2 ∣ N^2 - (p.1.1^2 + p.1.2^2) := by")
out_lines.append("      intro hd")
out_lines.append("      have h_mod : (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd")
out_lines.append("      exact h_p_prop.2 h_mod")
out_lines.append("    have h_no_rep := not_sq_add_sq (N^2 - (p.1.1^2 + p.1.2^2)) p' h_prime_3mod4 h_dvd h_not_dvd")
out_lines.append("    exact h_no_rep h_two_sq")
out_lines.append("")

with open("Submission/Spec.lean", "w") as f:
    f.write("\n".join(row for row in out_lines))

print("SUCCESSFULLY GENERATED SPEC.LEAN!")
