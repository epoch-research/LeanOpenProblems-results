import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Nat

def primes_1414 : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409]

def remove_p_fuel (p : Nat) : Nat → Nat → Nat
  | 0, t => t
  | fuel + 1, t =>
    if t % p == 0 then remove_p_fuel p fuel (t / p) else t

def totient_list_loop : List Nat → Nat → Nat → Nat
  | [], temp, acc => if temp > 1 then acc - acc / temp else acc
  | p :: ps, temp, acc =>
    if p * p > temp then
      if temp > 1 then acc - acc / temp else acc
    else if temp % p == 0 then
      let acc' := acc - acc / p
      let temp' := remove_p_fuel p 32 temp
      totient_list_loop ps temp' acc'
    else
      totient_list_loop ps temp acc

def totient_fast (n : Nat) : Nat :=
  if n == 0 then 0
  else if n == 1 then 1
  else totient_list_loop primes_1414 n n

def sqrt_binary_loop (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, high => high
  | fuel + 1, low, high =>
    if low > high then high
    else
      let mid := (low + high) / 2
      let sq := mid * mid
      if sq == m then mid
      else if sq > m then
        if mid == 0 then low
        else sqrt_binary_loop m fuel low (mid - 1)
      else
        sqrt_binary_loop m fuel (mid + 1) high

def sqrt_fast (m : Nat) : Nat :=
  sqrt_binary_loop m 40 0 m

def is_square_fast (m : Nat) : Bool :=
  let r := sqrt_fast m
  r * r == m

def huge_nat_0 : Nat := 0x001400130041001000570038000d002f005400270004002d000a00080005004800020001001c005400550051001200150014000e001000090060001d000b005b0009000400cb00270014001300340010002b00190049002d002100970004002800120019001a000b003d000900070033003900480026000d007400360033003800090007003400520014001300010010004a002d0013001c0010000f00240004001100130006000400030082000e0005000e000200040003007d0007003a00090007001c0013003e00100038002100160034000d001100040054000b0028000a000800270005004b000100d9001f004000250011001900220020000a0008000c0005000e0002000100070014002b000f000a0008000a000500020001000200010001001d001300220010000f0021000e006d000900060004000300110037004b0073000a000800330005003f000200010021002100070037003d00160030003300f8001b0016001800250021001300260010000f0019004c003e001b00060004000300390041000c000a00be00140013003400100001007d0003002d00d1003d0004005a000d0083002000a3005100be003e0011001a007e000c0012001100080005001a0002000700170005000200010019000d0044001f002d0040001d00a30027005500230039007c00380043004a003000370085006f00120049005f000e003e00280009002000220020003200140013005d00a3001100c30016000c0022002000040022000500080002006d000200010011003d005f0014000a0008000c0005009300020001004200490001000400490097004000140013008c003d00180041002a0013001f00100004004a0041002100a50006000400030014001300200049001a000d001a00140013001500040011001300610010000a000800040005000d00020044002c005f004000480057001100480021001e004d00a300

def get_witness_from_tree (chunk_idx : Nat) (offset : Nat) : Nat :=
  (shiftRight huge_nat_0 (16 * offset) % 65536)

def get_uncovered_index (n : Nat) : Nat :=
  n - (n / 3 + n / 10 - n / 30) - 6

def get_witness_final (n : Nat) : Nat :=
  if n % 6 == 3 then n / 3
  else if n % 10 == 0 then n / 5
  else if n % 6 == 0 then
    if n % 30 == 0 then n / 10 else n / 6
  else
    let idx := get_uncovered_index n - 1
    get_witness_from_tree (idx / 5000) (idx % 5000)

def check_all_loop (primes : List Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, L, R =>
    if L > R then true
    else if L == R then
      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true
      else
        let k := get_witness_final L
        if k == 0 then false
        else if k > (L - 1) / 2 then false
        else is_square_fast (totient_fast k * totient_fast (L - k))
    else
      let mid := (L + R) / 2
      check_all_loop primes fuel L mid && check_all_loop primes fuel (mid + 1) R

theorem test_decide_0 : check_all_loop primes_1414 15 9 1008 = true := by
  decide
