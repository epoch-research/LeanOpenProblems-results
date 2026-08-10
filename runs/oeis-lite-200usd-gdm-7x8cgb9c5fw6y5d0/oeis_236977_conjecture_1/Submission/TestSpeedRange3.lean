import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Nat Finset

-- we use the standard totient_fast from Spec.lean
def totient_fast_loop (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
    if (i + 1).Coprime n then
      totient_fast_loop n i (acc + 1)
    else
      totient_fast_loop n i acc

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_fast_loop n (n - 1) 0

-- Standard definitions from Spec.lean
def get_index (n : Nat) : Nat :=
  let q := n / 30
  let r := n % 30
  let val := match r with
    | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 4 | 8 => 5 | 9 => 6
    | 10 => 6 | 11 => 6 | 12 => 7 | 13 => 7 | 14 => 8 | 15 => 9 | 16 => 9 | 17 => 10 | 18 => 11 | 19 => 11
    | 20 => 12 | 21 => 12 | 22 => 12 | 23 => 13 | 24 => 14 | 25 => 14 | 26 => 15 | 27 => 16 | 28 => 16
    | _ => 17
  18 * q + val - 6

def hex_char_val (c : UInt8) : Nat :=
  if c ≥ 48 ∧ c ≤ 57 then (c - 48).toNat
  else if c ≥ 97 ∧ c ≤ 102 then (c - 87).toNat
  else 0

def decode_witness (bytes : ByteArray) (idx : Nat) : Nat :=
  if 4 * idx + 3 < bytes.size then
    let b0 := hex_char_val (bytes.get! (4 * idx))
    let b1 := hex_char_val (bytes.get! (4 * idx + 1))
    let b2 := hex_char_val (bytes.get! (4 * idx + 2))
    let b3 := hex_char_val (bytes.get! (4 * idx + 3))
    b0 * 4096 + b1 * 256 + b2 * 16 + b3
  else 0

def check_single (bytes : ByteArray) (n : Nat) : Bool :=
  if n % 6 = 3 ∨ n % 10 = 0 ∨ n % 6 = 0 then true
  else
    let idx := get_index n
    let k := decode_witness bytes idx
    if k = 0 ∨ k > (n - 1) / 2 then false
    else
      let m := totient_fast k * totient_fast (n - k)
      sqrt m ^ 2 == m

def check_all_loop (bytes : ByteArray) : Nat → Nat → Nat → Bool
  | 0, L, R =>
    if L = R then check_single bytes L else true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then check_single bytes L
    else
      let mid := (L + R) / 2
      check_all_loop bytes fuel L mid && check_all_loop bytes fuel (mid + 1) R

-- we read the witnesses_bytes from Spec
-- wait, we can just define a dummy or use a string
def witnesses_str : String := "00010001"
def witnesses_bytes : ByteArray := witnesses_str.toUTF8

theorem test_decide : check_all_loop witnesses_bytes 12 1000000 1001000 = true := by decide
