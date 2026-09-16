import Mathlib

def offset_C : ℤ := 4500
def max_C : ℤ := 13000
def max_F : ℤ := 22000

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
