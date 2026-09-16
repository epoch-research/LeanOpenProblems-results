import Mathlib

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000000

def offset_C : ℤ := 8500
def max_C : ℤ := 25000
def max_F : ℤ := 32000

def mkByteArray (n : Nat) : ByteArray :=
  ByteArray.mk (List.toArray (List.replicate n (0 : UInt8)))

def empty_arr : Array ByteArray :=
  List.toArray (List.replicate 32000 (mkByteArray 3150))

def set_bit (arr : Array ByteArray) (F C : ℤ) : Array ByteArray :=
  if F < 0 ∨ F ≥ max_F then arr
  else
    let C_idx := C + offset_C
    if C_idx < 0 ∨ C_idx ≥ max_C then arr
    else
      let f_idx := F.toNat
      let byte_idx := (C_idx.toNat) / 8
      let bit_idx := (C_idx.toNat) % 8
      let row := arr[f_idx]!
      let b := row[byte_idx]!
      let b' := b ||| (1 <<< bit_idx).toUInt8
      let row' := row.set! byte_idx b'
      arr.set! f_idx row'

def get_bit (arr : Array ByteArray) (F C : ℤ) : Bool :=
  if F < 0 ∨ F ≥ max_F then false
  else
    let C_idx := C + offset_C
    if C_idx < 0 ∨ C_idx ≥ max_C then false
    else
      let f_idx := F.toNat
      let byte_idx := (C_idx.toNat) / 8
      let bit_idx := (C_idx.toNat) % 8
      let row := arr[f_idx]!
      let b := row[byte_idx]!
      (b &&& (1 <<< bit_idx).toUInt8) ≠ 0

def bounds (F C : ℤ) : Bool :=
  F ≥ 91 ∧ 3 * F ≥ 5 * C ∧ 3 * F ≥ -7 * C

def process_pred (st : Array ByteArray × Array (ℤ × ℤ)) (F C : ℤ) : Array ByteArray × Array (ℤ × ℤ) :=
  if bounds F C ∧ ¬ get_bit st.1 F C then
    (set_bit st.1 F C, st.2.push (F, C))
  else st

def bfs_loop (fuel : ℕ) (st : Array ByteArray × Array (ℤ × ℤ)) (head : ℕ) : Array ByteArray × Array (ℤ × ℤ) :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
    if head ≥ st.2.size then st
    else
      let (F, C) := st.2[head]!
      let st1 := process_pred st (F - C) (-2 * C)
      let st2 := if F % 2 ≠ 0 then process_pred st1 (F - C) (F - 2 * C) else st1
      bfs_loop fuel' st2 (head + 1)

def init_st : Array ByteArray × Array (ℤ × ℤ) :=
  Id.run do
    let mut st := (empty_arr, #[])
    let C_init : List ℤ := [-2, -1, 1, 2]
    for C in C_init do
      for F in [91:26000] do
        if bounds F C then
          st := process_pred st F C
    return st

def final_st : Array ByteArray × Array (ℤ × ℤ) :=
  bfs_loop 800000 init_st 0

def is_closed (st : Array ByteArray × Array (ℤ × ℤ)) : Bool :=
  Id.run do
    let arr := st.1
    for (F, C) in st.2 do
      let F1 := F - C
      let C1 := -2 * C
      if bounds F1 C1 ∧ ¬ get_bit arr F1 C1 then
        return false
      if F % 2 ≠ 0 then
        let F2 := F - C
        let C2 := F - 2 * C
        if bounds F2 C2 ∧ ¬ get_bit arr F2 C2 then
          return false
    return true

def contains_targets (arr : Array ByteArray) : Bool :=
  Id.run do
    let C_init : List ℤ := [-2, 2]
    for C in C_init do
      for F in [91:26000] do
        if bounds F C ∧ ¬ get_bit arr F C then
          return false
    return true

def check_everything : Bool :=
  let st := final_st
  is_closed st ∧ ¬ get_bit st.1 91 46 ∧ contains_targets st.1

theorem everything_is_ok : check_everything = true := by
  decide
