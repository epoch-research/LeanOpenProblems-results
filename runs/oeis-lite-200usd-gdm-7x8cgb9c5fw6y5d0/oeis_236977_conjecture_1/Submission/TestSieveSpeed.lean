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
      let temp' := remove_p_fuel p temp temp
      totient_list_loop ps temp' acc'
    else
      totient_list_loop ps temp acc

def totient_fast (primes : List Nat) (n : Nat) : Nat :=
  if n == 0 then 0
  else if n == 1 then 1
  else totient_list_loop primes n n

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

def search_witness_loop_forward (primes : List Nat) (n : Nat) (limit : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k =>
    if k > limit then none
    else
      let prod := totient_fast primes k * totient_fast primes (n - k)
      if is_square_fast prod then some k
      else search_witness_loop_forward primes n limit fuel (k + 1)

def find_witness_forward (primes : List Nat) (n : Nat) : Option Nat :=
  search_witness_loop_forward primes n ((n - 1) / 2) 7000 1

def check_range : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, L, R =>
    if L > R then true
    else
      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then
        check_range fuel (L + 1) R
      else
        match find_witness_forward primes_1414 L with
        | some _ => check_range fuel (L + 1) R
        | none => false

theorem test_10k : check_range 10000 9 10000 = true := by
  decide
