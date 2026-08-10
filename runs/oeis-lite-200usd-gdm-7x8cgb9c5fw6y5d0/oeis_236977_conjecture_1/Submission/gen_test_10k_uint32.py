import math

limit = 10005
phi = list(range(limit))
for i in range(2, limit):
    if phi[i] == i:
        for j in range(i, limit, i):
            phi[j] -= phi[j] // i

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

def is_uncovered(n):
    if n % 6 == 3:
        return False
    if n % 10 == 0:
        return False
    if n % 6 == 0:
        return False
    return True

witnesses = []
for n in range(9, 10000 + 1):
    if is_uncovered(n):
        found = False
        for k in range(1, (n - 1) // 2 + 1):
            if is_square(phi[k] * phi[n - k]):
                witnesses.append(k)
                found = True
                break
        if not found:
            print(f"No witness for {n}!")
            exit(1)

hex_str = "".join(f"{w:04x}" for w in witnesses)

lean_code = f"""import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Option

def remove_p_fuel (p : UInt32) : Nat → UInt32 → UInt32
  | 0, t => t
  | fuel + 1, t =>
    if t % p == 0 then remove_p_fuel p fuel (t / p) else t

def totient_loop_fuel : Nat → UInt32 → UInt32 → UInt32 → UInt32
  | 0, _, _, acc => acc
  | fuel + 1, temp, p, acc =>
    if p * p > temp then
      if temp > 1 then acc - acc / temp else acc
    else if temp % p == 0 then
      let acc' := acc - acc / p
      let temp' := remove_p_fuel p 32 temp
      let next_p := if p == 2 then 3 else p + 2
      totient_loop_fuel fuel temp' next_p acc'
    else
      let next_p := if p == 2 then 3 else p + 2
      totient_loop_fuel fuel temp next_p acc

def totient_fast (n : UInt32) : UInt32 :=
  if n == 0 then 0
  else if n == 1 then 1
  else totient_loop_fuel 1500 n 2 n

def sqrt_binary_loop (m : UInt32) : Nat → UInt32 → UInt32 → UInt32
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

def sqrt_fast (m : UInt32) : UInt32 :=
  sqrt_binary_loop m 40 0 m

def is_square_fast (m : UInt32) : Bool :=
  let r := sqrt_fast m
  r * r == m

def hex_char_val (c : UInt8) : UInt32 :=
  if c ≥ 48 ∧ c ≤ 57 then (c - 48).toUInt32
  else if c ≥ 97 ∧ c ≤ 102 then (c - 87).toUInt32
  else 0

def decode_witness (bytes : ByteArray) (idx : Nat) : UInt32 :=
  let b0 := hex_char_val (bytes.get! (4 * idx))
  let b1 := hex_char_val (bytes.get! (4 * idx + 1))
  let b2 := hex_char_val (bytes.get! (4 * idx + 2))
  let b3 := hex_char_val (bytes.get! (4 * idx + 3))
  b0 * 4096 + b1 * 256 + b2 * 16 + b3

def all_witnesses_str : String := "{hex_str}"
def all_witnesses_bytes : ByteArray := all_witnesses_str.toUTF8

def check_all_loop : Nat → UInt32 → UInt32 → Nat → Option Nat
  | 0, _, _, idx => some idx
  | fuel + 1, L, R, idx =>
    if L > R then some idx
    else if L == R then
      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then
        some idx
      else
        let k := decode_witness all_witnesses_bytes idx
        if k == 0 ∨ k > (L - 1) / 2 then none
        else if is_square_fast (totient_fast k * totient_fast (L - k)) then
          some (idx + 1)
        else
          none
    else
      let mid := (L + R) / 2
      match check_all_loop fuel L mid idx with
      | none => none
      | some mid_idx => check_all_loop fuel (mid + 1) R mid_idx

theorem test_decide : (check_all_loop 20 9 10000 0).isSome = true := by
  decide
"""

with open("/workspace/leanproject/Submission/TestSpeed10k.lean", "w") as f:
    f.write(lean_code)

print("Generated TestSpeed10k.lean successfully!")
