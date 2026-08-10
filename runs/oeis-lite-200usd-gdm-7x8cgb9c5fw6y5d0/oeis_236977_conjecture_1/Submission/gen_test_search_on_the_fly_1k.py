def main():
    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("set_option maxRecDepth 200000")
    code.append("set_option maxHeartbeats 0")
    code.append("")
    code.append("open Nat")
    code.append("")
    
    # Primes list
    limit_primes = 1414
    is_p = [True] * (limit_primes + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, 38):
        if is_p[i]:
            for j in range(i*i, limit_primes + 1, i):
                is_p[j] = False
    primes_1414 = [p for p in range(limit_primes + 1) if is_p[p]]
    primes_str = ", ".join(f"{p}" for p in primes_1414)
    code.append(f"def primes_1414 : List UInt32 := [{primes_str}]")
    code.append("")

    # totient_fast with List recursion
    code.append("def remove_p_fuel (p : UInt32) : Nat → UInt32 → UInt32")
    code.append("  | 0, t => t")
    code.append("  | fuel + 1, t =>")
    code.append("    if t % p == 0 then remove_p_fuel p fuel (t / p) else t")
    code.append("")
    code.append("def totient_list_loop : List UInt32 → UInt32 → UInt32 → UInt32")
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
    code.append("def totient_fast (n : UInt32) : UInt32 :=")
    code.append("  if n == 0 then 0")
    code.append("  else if n == 1 then 1")
    code.append("  else totient_list_loop primes_1414 n n")
    code.append("")

    # sqrt_fast and is_square_fast with UInt32
    code.append("def sqrt_binary_loop (m : UInt32) : Nat → UInt32 → UInt32 → UInt32")
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
    code.append("def sqrt_fast (m : UInt32) : UInt32 :=")
    code.append("  sqrt_binary_loop m 40 0 m")
    code.append("")
    code.append("def is_square_fast (m : UInt32) : Bool :=")
    code.append("  let r := sqrt_fast m")
    code.append("  r * r == m")
    code.append("")

    # find_partition on-the-fly search
    code.append("def find_partition_loop (n : UInt32) : Nat → UInt32 → Bool")
    code.append("  | 0, _ => false")
    code.append("  | fuel + 1, k =>")
    code.append("    if k > (n - 1) / 2 then false")
    code.append("    else if is_square_fast (totient_fast k * totient_fast (n - k)) then true")
    code.append("    else find_partition_loop n fuel (k + 1)")
    code.append("")
    code.append("def find_partition (n : UInt32) : Bool :=")
    code.append("  find_partition_loop n 1000 1")
    code.append("")

    # check_all_loop
    code.append("def check_all_loop : Nat → Nat → Nat → Bool")
    code.append("  | 0, _, _ => true")
    code.append("  | fuel + 1, L, R =>")
    code.append("    if L > R then true")
    code.append("    else if L == R then")
    code.append("      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true")
    code.append("      else find_partition L.toUInt32")
    code.append("    else")
    code.append("      let mid := (L + R) / 2")
    code.append("      check_all_loop fuel L mid && check_all_loop fuel (mid + 1) R")
    code.append("")

    code.append("theorem test_decide : check_all_loop 25 9 1000 = true := by")
    code.append("  decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestSearchOnTheFly1k.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated successfully!")

if __name__ == "__main__":
    main()
