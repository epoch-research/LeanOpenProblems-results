import re
import sys
sys.set_int_max_str_digits(200000)
from sympy import isprime
from sympy.ntheory.modular import crt

# Old counterexample from iterative_out.txt
n_old = 126686524250410004736537312064293613795653657092983804510554503324715379258723493119883344012301288982405926046569374575432235100014312858069895494644651006289334684761526421296266808332923548185778355634967387614240536269449875614849275
n2 = n_old*n_old

# Read extra primes from expand_out.txt
with open("/workspace/leanproject/Submission/expand_out.txt") as f:
    content = f.read()

match = re.search(r"Extra primes:\s*(\[.*\])", content)
if not match:
    print("Could not find Extra primes in expand_out.txt!")
    exit(1)

extra_primes_str = match.group(1)
try:
    extra_primes = eval(extra_primes_str)
except Exception:
    pairs = re.findall(r"\((\d+),?\s*(\d+)\)", extra_primes_str)
    extra_primes = [(int(p), int(r)) for p, r in pairs]

used_primes = [(26, 11), (104, 19), (314, 31), (416, 23), (1256, 43), (1664, 59), (5024, 47), (6656, 67), (20096, 71), (26624, 79), (73274, 83), (80384, 107), (106496, 103), (293096, 127), (425984, 163), (1286144, 131), (1703936, 191), (4689536, 151), (6815744, 199), (18758144, 167), (75032576, 223), (82313216, 139), (109051904, 227), (300130304, 251), (436207616, 263), (1317011456, 179), (5268045824, 211), (6979321856, 307), (19208339456, 311), (21072183296, 239), (84288733184, 379), (111669149696, 331), (307333431296, 383), (446676598784, 367), (1348619730944, 431), (1786706395136, 439), (4917334900736, 419), (5394478923776, 443), (19669339602944, 463), (86311662780416, 487), (114349209288704, 499), (457396837154816, 503), (1380986604486656, 491), (1829587348619264, 587), (20141403753414656, 467), (22095785671786496, 563), (80565615013658624, 479), (88383142687145984, 631), (322262460054634496, 523), (5156199360874151936, 571), (20624797443496607744, 599)]

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

moduli = [9, 49]
residues = [1, 15]

for v, p in used_primes:
    moduli.append(p**2)
    residues.append(n_old % (p**2))

for p, r in extra_primes:
    moduli.append(p**2)
    root = -1
    for x in range(p):
        if (x*x) % p == r % p:
            root = x
            break
    V_temp = get_V_all(10**300)
    covered_vs = [v for v in V_temp if v % p == r]
    
    best_k = -1
    best_fail_count = 999999
    for k in range(p):
        x = root + k*p
        fail_count = 0
        for fv in covered_vs:
            if (x*x - fv) % (p**2) == 0:
                fail_count += 1
        if fail_count < best_fail_count:
            best_fail_count = fail_count
            best_k = k
            
    lift = root + best_k * p
    residues.append(lift)

print("Solving CRT...")
n0, prod = crt(moduli, residues)
n0 = int(n0)
prod = int(prod)
if n0 % 2 == 0:
    n0 += prod

n0_sq = n0 * n0
V_all = get_V_all(n0_sq)
print(f"n0 = {n0}")
print(f"V_all size: {len(V_all)}")

primes_check = [3, 7] + [p for _, p in used_primes] + [p for p, _ in extra_primes]

v_to_prime = {}
for v in V_all:
    val = n0_sq - v
    found = False
    for p in primes_check:
        if val % p == 0 and val % (p*p) != 0:
            v_to_prime[v] = p
            found = True
            break
    if not found:
        print(f"Error: v = {v} is not blocked by any prime!")
        sys.exit(1)

# Now, map each v to an index
v_to_idx = {}
for v in V_all:
    if v == 1:
        v_to_idx[v] = 6400
    else:
        found = False
        for s_val in range(40):
            fs = (10 * 16**s_val + 16 * 4**s_val + 10) // 9
            if v % fs == 0:
                ratio = v // fs
                # Is ratio a power of 4?
                if ratio > 0 and (ratio & (ratio - 1)) == 0:
                    i_val = ratio.bit_length() - 1
                    if i_val % 2 == 0:
                        i_val //= 2
                        if i_val < 160:
                            v_to_idx[v] = i_val * 40 + s_val
                            found = True
                            break
        if not found:
            print(f"Error: could not find indices for v = {v}!")
            sys.exit(1)

# Build a list of (idx, prime) pairs
idx_to_prime = {}
for v, p in v_to_prime.items():
    idx = v_to_idx[v]
    idx_to_prime[idx] = p

# Generate sorted list of idx's from 0 to 6400
all_idxs = sorted(list(idx_to_prime.keys()))
assert len(all_idxs) == 6401
assert all_idxs[0] == 0 and all_idxs[-1] == 6400

# Chunk size for idx's
chunk_size = 50
chunks = [all_idxs[i:i + chunk_size] for i in range(0, len(all_idxs), chunk_size)]

out_lines = [
    "/-",
    "Copyright 2026 The Formal Conjectures Authors.",
    "-/",
    "import FormalConjectures.Util.ProblemImports",
    "",
    "set_option linter.style.namespace false",
    "",
    "open Nat Finset Int",
    "set_option maxRecDepth 10000",
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
    "    ∃ u v : ℕ, u + v = 2 * k ∧ u ≤ v ∧ 36 * (x^2 + y^2) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by",
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
    "  have h_uv_le : u ≤ v := by",
    "    have h_pow_le : 2^u ≤ 2^v := by",
    "      rw [← hu_eq, ← hv_eq]",
    "      omega",
    "    rwa [Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h_pow_le",
    "  use u, v",
    "  refine ⟨h_uv, h_uv_le, ?_⟩",
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
    out_lines.append(f"def blocking_prime_by_idx_{chunk_idx} (idx : ℕ) : ℕ :=")
    out_lines.append("  match idx with")
    for idx in chunk:
        p = idx_to_prime[idx]
        out_lines.append(f"  | {idx} => {p}")
    out_lines.append("  | _ => 3")
    out_lines.append("")
    out_lines.append(f"lemma blocking_prime_by_idx_{chunk_idx}_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx_{chunk_idx} idx) :=")
    out_lines.append(f"  by unfold blocking_prime_by_idx_{chunk_idx}; split <;> norm_num")
    out_lines.append("")
    out_lines.append(f"lemma blocking_prime_by_idx_{chunk_idx}_3mod4 (idx : ℕ) : blocking_prime_by_idx_{chunk_idx} idx % 4 = 3 :=")
    out_lines.append(f"  by unfold blocking_prime_by_idx_{chunk_idx}; split <;> decide")
    out_lines.append("")

# Now, the main blocking_prime_by_idx function
blocking_prime_lines = [
    "def blocking_prime_by_idx (idx : ℕ) : ℕ :=",
    "  match idx / 50 with"
]
for chunk_idx, chunk in enumerate(chunks[:-1]):
    blocking_prime_lines.append(f"  | {chunk_idx} => blocking_prime_by_idx_{chunk_idx} idx")
blocking_prime_lines.append(f"  | _ => blocking_prime_by_idx_{len(chunks)-1} idx")
blocking_prime_lines.append("")
out_lines.extend(blocking_prime_lines)

# Proof of primality for main blocking_prime_by_idx
blocking_prime_prime_lines = [
    "lemma blocking_prime_by_idx_prime (idx : ℕ) : Nat.Prime (blocking_prime_by_idx idx) :=",
    "  by",
    "    unfold blocking_prime_by_idx",
    "    split"
]
for chunk_idx, chunk in enumerate(chunks[:-1]):
    blocking_prime_prime_lines.append(f"    · exact blocking_prime_by_idx_{chunk_idx}_prime idx")
blocking_prime_prime_lines.append(f"    · exact blocking_prime_by_idx_{len(chunks)-1}_prime idx")
blocking_prime_prime_lines.append("")
out_lines.extend(blocking_prime_prime_lines)

# Proof of 3 mod 4 for main blocking_prime_by_idx
blocking_prime_3mod4_lines = [
    "lemma blocking_prime_by_idx_3mod4 (idx : ℕ) : blocking_prime_by_idx idx % 4 = 3 :=",
    "  by",
    "    unfold blocking_prime_by_idx",
    "    split"
]
for chunk_idx, chunk in enumerate(chunks[:-1]):
    blocking_prime_3mod4_lines.append(f"    · exact blocking_prime_by_idx_{chunk_idx}_3mod4 idx")
blocking_prime_3mod4_lines.append(f"    · exact blocking_prime_by_idx_{len(chunks)-1}_3mod4 idx")
blocking_prime_3mod4_lines.append("")
out_lines.extend(blocking_prime_3mod4_lines)

# Generate is_blocked_by_idx
out_lines.append("def is_blocked_by_idx (idx : ℕ) : Bool :=")
out_lines.append("  let p := blocking_prime_by_idx idx")
out_lines.append("  let v := if idx = 6400 then 1 else 4^(idx / 40) * (10 * 16^(idx % 40) + 16 * 4^(idx % 40) + 10) / 9")
out_lines.append("  (N^2 - v) % p == 0 && (N^2 - v) % (p^2) != 0")
out_lines.append("")

# Generate is_blocked theorems
# Generate is_blocked theorems in chunks of 1000 to prevent stack overflow in kernel evaluation
out_lines.append("lemma is_blocked_chunk_0 : ∀ idx < 1000, is_blocked_by_idx idx = true := by decide")
out_lines.append("lemma is_blocked_chunk_1 : ∀ idx < 1000, is_blocked_by_idx (idx + 1000) = true := by decide")
out_lines.append("lemma is_blocked_chunk_2 : ∀ idx < 1000, is_blocked_by_idx (idx + 2000) = true := by decide")
out_lines.append("lemma is_blocked_chunk_3 : ∀ idx < 1000, is_blocked_by_idx (idx + 3000) = true := by decide")
out_lines.append("lemma is_blocked_chunk_4 : ∀ idx < 1000, is_blocked_by_idx (idx + 4000) = true := by decide")
out_lines.append("lemma is_blocked_chunk_5 : ∀ idx < 1000, is_blocked_by_idx (idx + 5000) = true := by decide")
out_lines.append("lemma is_blocked_chunk_6 : ∀ idx < 401, is_blocked_by_idx (idx + 6000) = true := by decide")
out_lines.append("")
out_lines.append("theorem is_blocked_all : ∀ idx < 6401, is_blocked_by_idx idx = true := by")
out_lines.append("  intro idx h_lt")
out_lines.append("  have h_cases : idx < 1000 ∨ (idx ≥ 1000 ∧ idx < 2000) ∨ (idx ≥ 2000 ∧ idx < 3000) ∨ (idx ≥ 3000 ∧ idx < 4000) ∨ (idx ≥ 4000 ∧ idx < 5000) ∨ (idx ≥ 5000 ∧ idx < 6000) ∨ (idx ≥ 6000) := by omega")
out_lines.append("  rcases h_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6")
out_lines.append("  · exact is_blocked_chunk_0 idx h0")
out_lines.append("  · have : idx - 1000 < 1000 := by omega")
out_lines.append("    have h_eq : idx = (idx - 1000) + 1000 := by omega")
out_lines.append("    rw [h_eq]")
out_lines.append("    exact is_blocked_chunk_1 (idx - 1000) this")
out_lines.append("  · have : idx - 2000 < 1000 := by omega")
out_lines.append("    have h_eq : idx = (idx - 2000) + 2000 := by omega")
out_lines.append("    rw [h_eq]")
out_lines.append("    exact is_blocked_chunk_2 (idx - 2000) this")
out_lines.append("  · have : idx - 3000 < 1000 := by omega")
out_lines.append("    have h_eq : idx = (idx - 3000) + 3000 := by omega")
out_lines.append("    rw [h_eq]")
out_lines.append("    exact is_blocked_chunk_3 (idx - 3000) this")
out_lines.append("  · have : idx - 4000 < 1000 := by omega")
out_lines.append("    have h_eq : idx = (idx - 4000) + 4000 := by omega")
out_lines.append("    rw [h_eq]")
out_lines.append("    exact is_blocked_chunk_4 (idx - 4000) this")
out_lines.append("  · have : idx - 5000 < 1000 := by omega")
out_lines.append("    have h_eq : idx = (idx - 5000) + 5000 := by omega")
out_lines.append("    rw [h_eq]")
out_lines.append("    exact is_blocked_chunk_5 (idx - 5000) this")
out_lines.append("  · have : idx - 6000 < 401 := by omega")
out_lines.append("    have h_eq : idx = (idx - 6000) + 6000 := by omega")
out_lines.append("    rw [h_eq]")
out_lines.append("    exact is_blocked_chunk_6 (idx - 6000) this")
out_lines.append("")

# Generate helper lemma for algebraic identity
out_lines.append("lemma h_id_int_lemma (p : (ℕ × ℕ) × ℕ × ℕ) (k u v_pow : ℕ) (h_uv : u + v_pow = 2 * k) (h_eq_class : 36 * (p.1.1^2 + p.1.2^2) = 10 * 2^(2*v_pow) + 16 * 2^(2*k) + 10 * 2^(2*u)) (hu_ge : u ≥ 1) (h_u_le_k : u ≤ k) : 9 * (p.1.1^2 + p.1.2^2) = 4^(u - 1) * (10 * 16^(k - u) + 16 * 4^(k - u) + 10) := by")
out_lines.append("  let i := u - 1")
out_lines.append("  let s := k - u")
out_lines.append("  have h_id_int' : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (4 * (4^i * (10 * 16^s + 16 * 4^s + 10)) : ℤ) := by")
out_lines.append("    have h_eq_class_cast : (36 * (p.1.1^2 + p.1.2^2) : ℤ) = (10 * 2^(2*v_pow) + 16 * 2^(2*k) + 10 * 2^(2*u) : ℤ) := by exact_mod_cast h_eq_class")
out_lines.append("    rw [h_eq_class_cast]")
out_lines.append("    have h_16 : (16^s : ℤ) = 2^(4 * s) := by")
out_lines.append("      have : (16^s : ℕ) = 2^(4 * s) := by rw [show 16 = 2^4 by rfl, ← pow_mul]")
out_lines.append("      exact_mod_cast this")
out_lines.append("    have h_4s : (4^s : ℤ) = 2^(2 * s) := by")
out_lines.append("      have : (4^s : ℕ) = 2^(2 * s) := by rw [show 4 = 2^2 by rfl, ← pow_mul]")
out_lines.append("      exact_mod_cast this")
out_lines.append("    have h_4i : (4^i : ℤ) = 2^(2 * i) := by")
out_lines.append("      have : (4^i : ℕ) = 2^(2 * i) := by rw [show 4 = 2^2 by rfl, ← pow_mul]")
out_lines.append("      exact_mod_cast this")
out_lines.append("    rw [h_16, h_4s, h_4i]")
out_lines.append("    have h1 : (2^(2 * v_pow) : ℤ) = 2^(2 * i + 2 + 4 * s) := by")
out_lines.append("      have : 2 * v_pow = 2 * i + 2 + 4 * s := by omega")
out_lines.append("      rw [this]")
out_lines.append("    have h2 : (2^(2 * k) : ℤ) = 2^(2 * i + 2 + 2 * s) := by")
out_lines.append("      have : 2 * k = 2 * i + 2 + 2 * s := by omega")
out_lines.append("      rw [this]")
out_lines.append("    have h3 : (2^(2 * u) : ℤ) = 2^(2 * i + 2) := by")
out_lines.append("      have : 2 * u = 2 * i + 2 := by omega")
out_lines.append("      rw [this]")
out_lines.append("    rw [h1, h2, h3]")
out_lines.append("    repeat rw [pow_add]")
out_lines.append("    ring")
out_lines.append("  have h_id_nat : 36 * (p.1.1^2 + p.1.2^2) = 4 * (4^i * (10 * 16^s + 16 * 4^s + 10)) := by")
out_lines.append("    exact_mod_cast h_id_int'")
out_lines.append("  omega")
out_lines.append("")

# Generate main disproof
out_lines.append("theorem A301376_conjecture.disproof : ¬ ∀ (n : ℕ), n > 0 → a n > 0 := by")
out_lines.append("  intro h")
out_lines.append("  have h_pos : N > 0 := by decide")
out_lines.append("  have h_a := h N h_pos")
out_lines.append("  have h_a' : 0 < a N := h_a")
out_lines.append("  unfold a at h_a'")
out_lines.append("  dsimp only at h_a'")
out_lines.append("  rw [Finset.card_pos, Finset.filter_nonempty_iff] at h_a'")
out_lines.append("  obtain ⟨p, hp⟩ := h_a'")
out_lines.append("  rcases hp with ⟨h_dom, h_sum, h_zw, k, hk_mem, hk_eq⟩")
out_lines.append("  obtain ⟨u, v_pow, h_uv, h_le_v, h_eq_class⟩ := classification_step p.1.1 p.1.2 k hk_eq")
out_lines.append("  have h_cases : u = 0 ∨ u ≥ 1 := by omega")
out_lines.append("  rcases h_cases with rfl | hu_ge")
out_lines.append("  · -- Case u = 0")
out_lines.append("    have h_k_cases : k = 0 ∨ k ≥ 1 := by omega")
out_lines.append("    rcases h_k_cases with rfl | hk_ge")
out_lines.append("    · -- Subcase k = 0")
out_lines.append("      have h_v0 : v_pow = 0 := by omega")
out_lines.append("      subst h_v0")
out_lines.append("      have h_sum_class : 36 * (p.1.1^2 + p.1.2^2) = 36 := by")
out_lines.append("        rw [h_eq_class]")
out_lines.append("        rfl")
out_lines.append("      have h_v_one : p.1.1^2 + p.1.2^2 = 1 := by omega")
out_lines.append("      have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - 1 := by")
out_lines.append("        use p.2.1, p.2.2")
out_lines.append("        omega")
out_lines.append("      have h_blocked : is_blocked_by_idx 6400 = true := is_blocked_all 6400 (by decide)")
out_lines.append("      unfold is_blocked_by_idx at h_blocked")
out_lines.append("      dsimp only at h_blocked")
out_lines.append("      have h_p_prop : (N^2 - 1) % (blocking_prime_by_idx 6400) = 0 ∧ (N^2 - 1) % (blocking_prime_by_idx 6400)^2 ≠ 0 := by")
out_lines.append("        rw [Bool.and_eq_true] at h_blocked")
out_lines.append("        exact ⟨beq_iff_eq.mp h_blocked.1, bne_iff_ne.mp h_blocked.2⟩")
out_lines.append("      let p' := blocking_prime_by_idx 6400")
out_lines.append("      have h_prime_fact : Fact (Nat.Prime p') := ⟨blocking_prime_by_idx_prime 6400⟩")
out_lines.append("      have h_prime_3mod4 : p' % 4 = 3 := blocking_prime_by_idx_3mod4 6400")
out_lines.append("      have h_dvd : p' ∣ N^2 - 1 := Nat.dvd_of_mod_eq_zero h_p_prop.1")
out_lines.append("      have h_not_dvd : ¬ p'^2 ∣ N^2 - 1 := by")
out_lines.append("        intro hd")
out_lines.append("        have h_mod : (N^2 - 1) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd")
out_lines.append("        exact h_p_prop.2 h_mod")
out_lines.append("      have h_no_rep := not_sq_add_sq (N^2 - 1) p' h_prime_3mod4 h_dvd h_not_dvd")
out_lines.append("      exact h_no_rep h_two_sq")
out_lines.append("    · -- Subcase k >= 1")
out_lines.append("      have h_v_eq : v_pow = 2 * k := by omega")
out_lines.append("      rw [h_v_eq] at h_eq_class")
out_lines.append("      have h_rhs_mod : (10 * 2^(2 * (2 * k)) + 16 * 2^(2 * k) + 10 * 2^(2 * 0)) % 4 = 2 := by")
out_lines.append("        have h_k_ge : 2 * k ≥ 2 := by omega")
out_lines.append("        have h_pow1 : 4 ∣ 2^(2 * (2 * k)) := by")
out_lines.append("          have : 2^(2 * (2 * k)) = 4^(2 * k) := by")
out_lines.append("            rw [show 2^(2 * (2 * k)) = (2^2)^(2 * k) by rw [← pow_mul, mul_comm]]")
out_lines.append("            rfl")
out_lines.append("          rw [this]")
out_lines.append("          use 4^(2 * k - 1)")
out_lines.append("          have : 2 * k = (2 * k - 1) + 1 := by omega")
out_lines.append("          nth_rw 1 [this]")
out_lines.append("          rw [pow_add]")
out_lines.append("          ring")
out_lines.append("        have h_pow2 : 4 ∣ 2^(2 * k) := by")
out_lines.append("          have : 2^(2 * k) = 4^k := by")
out_lines.append("            rw [show 2^(2 * k) = (2^2)^k by rw [← pow_mul, mul_comm]]")
out_lines.append("            rfl")
out_lines.append("          rw [this]")
out_lines.append("          use 4^(k - 1)")
out_lines.append("          have : k = (k - 1) + 1 := by omega")
out_lines.append("          nth_rw 1 [this]")
out_lines.append("          rw [pow_add]")
out_lines.append("          ring")
out_lines.append("        omega")
out_lines.append("      have h_lhs_mod : (36 * (p.1.1^2 + p.1.2^2)) % 4 = 0 := by omega")
out_lines.append("      omega")
out_lines.append("  · -- Case u >= 1")
out_lines.append("    let i := u - 1")
out_lines.append("    let s := k - u")
out_lines.append("    have h_s_bounds : s < 40 := by")
out_lines.append("      by_contra hc")
out_lines.append("      push_neg at hc")
out_lines.append("      have h_pow16 : 10 * 16^s ≥ 10 * 16^40 := by")
out_lines.append("        gcongr")
out_lines.append("        omega")
out_lines.append("      have h_val_ge : 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 ≥ 10 * 16^40 / 9 := by")
out_lines.append("        have : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 10 * 16^s := by")
out_lines.append("          have hA : 4^i ≥ 1 := by")
out_lines.append("            have : 4^i > 0 := by positivity")
out_lines.append("            omega")
out_lines.append("          have hB : 10 * 16^s + 16 * 4^s + 10 ≥ 10 * 16^s := by omega")
out_lines.append("          nlinarith")
out_lines.append("        omega")
out_lines.append("      have h_v_bound : p.1.1^2 + p.1.2^2 ≥ N^2 := by")
out_lines.append("        have h_u_le_k : u ≤ k := by omega")
out_lines.append("        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k")
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
out_lines.append("        have h_u_le_k : u ≤ k := by omega")
out_lines.append("        have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k")
out_lines.append("        have h_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by")
out_lines.append("          rw [← h_eq_class']")
out_lines.append("          rw [Nat.mul_div_cancel_left]")
out_lines.append("          decide")
out_lines.append("        rw [h_div]")
out_lines.append("        omega")
out_lines.append("      omega")
out_lines.append("    have h_u_le_k : u ≤ k := by omega")
out_lines.append("    have h_eq_class' : 9 * (p.1.1^2 + p.1.2^2) = 4^i * (10 * 16^s + 16 * 4^s + 10) := h_id_int_lemma p k u v_pow h_uv h_eq_class hu_ge h_u_le_k")
out_lines.append("    have h_v_div : p.1.1^2 + p.1.2^2 = 4^i * (10 * 16^s + 16 * 4^s + 10) / 9 := by")
out_lines.append("      rw [← h_eq_class']")
out_lines.append("      rw [Nat.mul_div_cancel_left]")
out_lines.append("      decide")
out_lines.append("    have h_two_sq : ∃ z w, z^2 + w^2 = N^2 - (p.1.1^2 + p.1.2^2) := by")
out_lines.append("      use p.2.1, p.2.2")
out_lines.append("      omega")
out_lines.append("    let idx := i * 40 + s")
out_lines.append("    have h_idx_lt : idx < 6401 := by omega")
out_lines.append("    have h_div_idx : idx / 40 = i := by omega")
out_lines.append("    have h_mod_idx : idx % 40 = s := by omega")
out_lines.append("    have h_blocked : is_blocked_by_idx idx = true := is_blocked_all idx h_idx_lt")
out_lines.append("    unfold is_blocked_by_idx at h_blocked")
out_lines.append("    have h_not_6400 : idx ≠ 6400 := by omega")
out_lines.append("    split_ifs at h_blocked")
out_lines.append("    · contradiction")
out_lines.append("    · rw [h_div_idx, h_mod_idx, h_v_div] at h_blocked")
out_lines.append("      let p' := blocking_prime_by_idx idx")
out_lines.append("      have h_p_prop : (N^2 - (p.1.1^2 + p.1.2^2)) % p' = 0 ∧ (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 ≠ 0 := by")
out_lines.append("        rw [Bool.and_eq_true] at h_blocked")
out_lines.append("        exact ⟨beq_iff_eq.mp h_blocked.1, bne_iff_ne.mp h_blocked.2⟩")
out_lines.append("      have h_prime_fact : Fact (Nat.Prime p') := ⟨blocking_prime_by_idx_prime idx⟩")
out_lines.append("      have h_prime_3mod4 : p' % 4 = 3 := blocking_prime_by_idx_3mod4 idx")
out_lines.append("      have h_dvd : p' ∣ N^2 - (p.1.1^2 + p.1.2^2) := Nat.dvd_of_mod_eq_zero h_p_prop.1")
out_lines.append("      have h_not_dvd : ¬ p'^2 ∣ N^2 - (p.1.1^2 + p.1.2^2) := by")
out_lines.append("        intro hd")
out_lines.append("        have h_mod : (N^2 - (p.1.1^2 + p.1.2^2)) % p'^2 = 0 := Nat.mod_eq_zero_of_dvd hd")
out_lines.append("        exact h_p_prop.2 h_mod")
out_lines.append("      have h_no_rep := not_sq_add_sq (N^2 - (p.1.1^2 + p.1.2^2)) p' h_prime_3mod4 h_dvd h_not_dvd")
out_lines.append("      exact h_no_rep h_two_sq")
out_lines.append("")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("\n".join(row for row in out_lines))

print("SUCCESSFULLY GENERATED INDEXED SPEC.LEAN!")
