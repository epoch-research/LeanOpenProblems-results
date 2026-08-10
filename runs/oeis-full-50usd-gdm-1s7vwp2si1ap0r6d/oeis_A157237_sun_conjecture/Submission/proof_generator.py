def get_divisor(p):
    if p < 2:
        return None
    for d in range(2, int(p**0.5) + 1):
        if p % d == 0:
            return d
    return None

def generate_proof_for_n(n):
    N = 2 * n - 1
    import math
    B = int(math.log2(N)) + 1 if N > 0 else 1
    
    proof_lines = []
    proof_lines.append(f"theorem a_eq_zero_{n} : a {n} = 0 := by")
    proof_lines.append(f"  dsimp [a]")
    proof_lines.append(f"  apply Finset.sum_eq_zero")
    proof_lines.append(f"  intro pair h_mem")
    proof_lines.append(f"  rcases pair with ⟨x, y⟩")
    proof_lines.append(f"  simp only [Finset.mem_product, Finset.mem_Icc] at h_mem")
    proof_lines.append(f"  rcases h_mem with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩")
    proof_lines.append(f"  change x ≤ {B} at hx2")
    proof_lines.append(f"  change y ≤ {B} at hy2")
    proof_lines.append(f"  interval_cases x")
    
    for x in range(1, B + 1):
        proof_lines.append(f"  · -- x = {x}")
        proof_lines.append(f"    interval_cases y")
        for y in range(1, B + 1):
            proof_lines.append(f"    · -- y = {y}")
            S = 2**x + 11 * 2**y
            if N <= S:
                proof_lines.append(f"      rfl")
            else:
                p = N - S
                if p % 6 != 1:
                    proof_lines.append(f"      rfl")
                else:
                    if p < 2:
                        lemma = "Nat.not_prime_one" if p == 1 else "Nat.not_prime_zero"
                        proof_lines.append(f"      have h_not_prime : ¬ Nat.Prime {p} := {lemma}")
                        proof_lines.append(f"      have h_and : ¬ (Nat.Prime {p} ∧ {p} % 6 = 1) := fun h => h_not_prime h.1")
                        proof_lines.append(f"      change (if Nat.Prime {p} ∧ {p} % 6 = 1 then 1 else 0) = 0")
                        proof_lines.append(f"      rw [if_neg h_and]")
                    else:
                        d = get_divisor(p)
                        if d is None:
                            raise ValueError(f"Error: {p} is prime for n = {n}, x = {x}, y = {y}!")
                        proof_lines.append(f"      have h_not_prime : ¬ Nat.Prime {p} := by")
                        proof_lines.append(f"        apply Nat.not_prime_of_dvd_of_lt (m := {d})")
                        proof_lines.append(f"        · decide") # d | p
                        proof_lines.append(f"        · decide") # 2 <= d
                        proof_lines.append(f"        · decide") # d < p
                        proof_lines.append(f"      have h_and : ¬ (Nat.Prime {p} ∧ {p} % 6 = 1) := fun h => h_not_prime h.1")
                        proof_lines.append(f"      change (if Nat.Prime {p} ∧ {p} % 6 = 1 then 1 else 0) = 0")
                        proof_lines.append(f"      rw [if_neg h_and]")
                    
    return "\n".join(proof_lines)

known_zeros = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 21, 24, 51, 84, 1011, 59586]
for z in known_zeros:
    print(f"Generating proof for {z}...")
    proof = generate_proof_for_n(z)
    with open(f"/workspace/leanproject/Submission/proof_{z}.lean", "w") as f:
        f.write("import FormalConjectures.Util.ProblemImports\nopen Nat\n\n" + proof + "\n")
print("Done!")
