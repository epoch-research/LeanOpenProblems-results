import math

def main():
    # Primes list
    limit_primes = 1414
    is_p = [True] * (limit_primes + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(math.isqrt(limit_primes)) + 1):
        if is_p[i]:
            for j in range(i*i, limit_primes + 1, i):
                is_p[j] = False
    primes_1414 = [p for p in range(limit_primes + 1) if is_p[p]]

    # Let us read the witnesses from witnesses.hex
    with open("/workspace/leanproject/Submission/witnesses.hex", "r") as f:
        hex_str = f.read().strip()

    # Convert to 5000-size Nat chunks
    # Note: witnesses.hex contains hex_str. Number of witnesses = len(hex_str)//4
    witnesses = [int(hex_str[i:i+4], 16) for i in range(0, len(hex_str), 4)]
    
    chunk_size = 5000
    chunks = []
    for i in range(0, len(witnesses), chunk_size):
        chunks.append(witnesses[i:i+chunk_size])

    huge_nats = []
    for chunk in chunks:
        val = 0
        for i, w in enumerate(chunk):
            val |= (int(w) & 0xFFFF) << (16 * i)
        huge_nats.append(f"0x{val:x}")

    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append("set_option maxHeartbeats 0")
    code.append("set_option maxRecDepth 200000")
    code.append("")
    code.append("open Nat")
    code.append("")
    code.append(f"def primes_1414 : List Nat := {str(primes_1414)}")
    code.append("")
    code.append("def remove_p_fuel (p : Nat) : Nat → Nat → Nat")
    code.append("  | 0, t => t")
    code.append("  | fuel + 1, t =>")
    code.append("    if t % p == 0 then remove_p_fuel p fuel (t / p) else t")
    code.append("")
    code.append("def totient_list_loop : List Nat → Nat → Nat → Nat")
    code.append("  | [], temp, acc => if temp > 1 then acc - acc / temp else acc")
    code.append("  | p :: ps, temp, acc =>")
    code.append("    if p * p > temp then")
    code.append("      if temp > 1 then acc - acc / temp else acc")
    code.append("    else if temp % p == 0 then")
    code.append("      let acc' := acc - acc / p")
    code.append("      let temp' := remove_p_fuel p 32 temp")
    code.append("      totient_list_loop ps temp' acc'")
    code.append("    else")
    code.append("      totient_list_loop ps temp acc")
    code.append("")
    code.append("def totient_fast (primes : List Nat) (n : Nat) : Nat :=")
    code.append("  if n == 0 then 0")
    code.append("  else if n == 1 then 1")
    code.append("  else totient_list_loop primes n n")
    code.append("")
    code.append("def sqrt_binary_loop (m : Nat) : Nat → Nat → Nat → Nat")
    code.append("  | 0, _, high => high")
    code.append("  | fuel + 1, low, high =>")
    code.append("    if low > high then high")
    code.append("    else")
    code.append("      let mid := (low + high) / 2")
    code.append("      let sq := mid * mid")
    code.append("      if sq == m then mid")
    code.append("      else if sq > m then")
    code.append("        if mid == 0 then low")
    code.append("        else sqrt_binary_loop m fuel low (mid - 1)")
    code.append("      else")
    code.append("        sqrt_binary_loop m fuel (mid + 1) high")
    code.append("")
    code.append("def sqrt_fast (m : Nat) : Nat :=")
    code.append("  sqrt_binary_loop m 40 0 m")
    code.append("")
    code.append("def is_square_fast (m : Nat) : Bool :=")
    code.append("  let r := sqrt_fast m")
    code.append("  r * r == m")
    code.append("")

    for i, hnat in enumerate(huge_nats):
        code.append(f"def huge_nat_{i} : Nat := {hnat}")
        code.append("")

    code.append("def get_witness_from_tree (chunk_idx : Nat) (offset : Nat) : Nat :=")
    def build_tree(L, R):
        if L == R:
            return f"(shiftRight huge_nat_{L} (16 * offset)) % 65536"
        mid = (L + R) // 2
        return f"(if chunk_idx ≤ {mid} then {build_tree(L, mid)} else {build_tree(mid + 1, R)})"
    
    code.append(f"  {build_tree(0, len(huge_nats) - 1)}")
    code.append("")

    code.append("def get_uncovered_index (n : Nat) : Nat :=")
    code.append("  n - (n / 3 + n / 10 - n / 30) - 6")
    code.append("")
    code.append("def get_witness_final (n : Nat) : Nat :=")
    code.append("  if n % 6 == 3 then n / 3")
    code.append("  else if n % 10 == 0 then n / 5")
    code.append("  else if n % 6 == 0 then")
    code.append("    if n % 30 == 0 then n / 10 else n / 6")
    code.append("  else")
    code.append("    let idx := get_uncovered_index n - 1")
    code.append("    get_witness_from_tree (idx / 5000) (idx % 5000)")
    code.append("")
    
    code.append("def check_all_loop (primes : List Nat) : Nat → Nat → Nat → Bool")
    code.append("  | 0, _, _ => true")
    code.append("  | fuel + 1, L, R =>")
    code.append("    if L > R then true")
    code.append("    else if L == R then")
    code.append("      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true")
    code.append("      else")
    code.append("        let k := get_witness_final L")
    code.append("        if k == 0 then false")
    code.append("        else if k > (L - 1) / 2 then false")
    code.append("        else is_square_fast (totient_fast primes k * totient_fast primes (L - k))")
    code.append("    else")
    code.append("      let mid := (L + R) / 2")
    code.append("      check_all_loop primes fuel L mid && check_all_loop primes fuel (mid + 1) R")
    code.append("")

    # Let's write the sequential proof
    # We check up to 20,000 (total 20 chunks of size 1000)
    # We will generate a single theorem check_all_sequential
    code.append("theorem check_all_sequential :")
    parts = []
    for i in range(20):
        L = 9 + i * 1000 if i == 0 else 1009 + (i-1) * 1000
        R = L + 999 if i == 0 else L + 999
        if R > 20000:
            R = 20000
        parts.append(f"(check_all_loop primes_1414 15 {L} {R} = true)")
    code.append("    " + " ∧\n    ".join(parts) + " :=")
    code.append("by")
    for i in range(20):
        L = 9 + i * 1000 if i == 0 else 1009 + (i-1) * 1000
        R = L + 999 if i == 0 else L + 999
        if R > 20000:
            R = 20000
        code.append(f"  have h{i} : check_all_loop primes_1414 15 {L} {R} = true := by decide")
    
    # Prove the conjunction
    conj = "⟨" + ", ".join(f"h{i}" for i in range(20)) + "⟩"
    code.append(f"  exact {conj}")
    code.append("")

    with open("/workspace/leanproject/Submission/TestSequential.lean", "w") as f:
        f.write("\n".join(code))
    print("TestSequential.lean written successfully!")

if __name__ == "__main__":
    main()
