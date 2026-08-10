import math

limit = 2000005
phi = list(range(limit))
for i in range(2, limit):
    if phi[i] == i:
        for j in range(i, limit, i):
            phi[j] -= phi[j] // i

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

uncovered = []
for n in range(9, limit):
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
    uncovered.append(n)

witnesses = []
for n in uncovered[:10000]:
    limit_k = (n - 1) // 2
    for k in range(1, limit_k + 1):
        if is_square(phi[k] * phi[n - k]):
            witnesses.append(k)
            break

# We only need the first 10,000 uncovered witnesses for our test
encoded_chars = []
for w in witnesses:
    c1 = 32 + w // 90
    c2 = 32 + w % 90
    encoded_chars.append(chr(c1) + chr(c2))

big_str = "".join(encoded_chars)
escaped_str = big_str.replace("\\", "\\\\").replace("\"", "\\\"")

code = []
code.append("import FormalConjectures.Util.ProblemImports")
code.append("")
code.append("set_option maxHeartbeats 0")
code.append("set_option maxRecDepth 200000")
code.append("")
code.append("open Nat")
code.append("")
code.append("def primes_1414 : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409]")
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
code.append("      let temp' := remove_p_fuel p temp temp")
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
code.append(f'def big_str : String := "{escaped_str}"')
code.append("")
code.append("def get_witness_from_string (idx : Nat) : Nat :=")
code.append("  let c1 := String.Pos.Raw.get big_str (String.Pos.Raw.mk (2 * idx))")
code.append("  let c2 := String.Pos.Raw.get big_str (String.Pos.Raw.mk (2 * idx + 1))")
code.append("  (c1.toNat - 32) * 90 + (c2.toNat - 32)")
code.append("")
code.append("def get_uncovered_index (n : Nat) : Nat :=")
code.append("  n - (n / 3 + n / 10 - n / 30) - 6")
code.append("")
code.append("def get_witness_final (n : Nat) : Nat :=")
code.append("  let idx := get_uncovered_index n - 1")
code.append("  get_witness_from_string idx")
code.append("")
code.append("def check_all_loop (primes : List Nat) : Nat → Nat → Nat → Bool")
code.append("  | 0, _, _ => true")
code.append("  | fuel + 1, L, R =>")
code.append("    if L > R then true")
code.append("    else if L == R then")
code.append("      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true")
code.append("      else")
code.append("        let k := get_witness_final L")
code.append("        let prod := totient_fast primes k * totient_fast primes (L - k)")
code.append("        is_square_fast prod")
code.append("    else")
code.append("      let mid := (L + R) / 2")
code.append("      check_all_loop primes fuel L mid && check_all_loop primes fuel (mid + 1) R")
code.append("")

max_n = uncovered[9999]
code.append(f"theorem test_10k : check_all_loop primes_1414 25 9 {max_n} = true := by")
code.append("  decide")
code.append("")

with open("/workspace/leanproject/Submission/TestSieveBinarySpeed.lean", "w") as f:
    f.write("\n".join(code))
