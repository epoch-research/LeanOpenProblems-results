import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

# We need the list of minimal multipliers k_q for each prime q <= 103
# Let us read the multipliers we computed earlier
multipliers = {
    2: 2, 3: 4, 5: 3, 7: 47, 11: 53, 13: 11, 17: 83, 19: 17, 23: 67, 29: 317,
    31: 29, 37: 257, 41: 367, 43: 41, 47: 233, 53: 157, 59: 293, 61: 59,
    67: 467, 71: 211, 73: 71, 79: 709, 83: 911, 89: 443, 97: 677, 101: 503,
    103: 101
}

output = []
output.append("lemma q_dvd_x_seq_q_sq_small (q : ℕ) (hq : Nat.Prime q) (hq_le : q ≤ 103) : q ∣ x_seq (q * q - 1) := by")
output.append("  interval_cases q")

for q in range(104):
    if is_prime(q):
        kq = multipliers[q]
        output.append(f"  · -- q = {q}")
        output.append(f"    have : {q} ∣ x_seq {kq} := by decide")
        output.append(f"    exact Nat.dvd_trans this (x_seq_dvd_x_seq_of_le (by decide) (by decide))")
    else:
        output.append(f"  · contradiction")

print("\n".join(output))
