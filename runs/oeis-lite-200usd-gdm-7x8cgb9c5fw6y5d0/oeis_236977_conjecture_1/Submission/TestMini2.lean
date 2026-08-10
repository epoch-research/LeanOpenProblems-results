def hex_char_val (c : Char) : Nat :=
  let val := c.toNat
  if val ≥ 48 ∧ val ≤ 57 then val - 48
  else if val ≥ 97 ∧ val ≤ 102 then val - 87
  else 0

def decode_witness (s : String) (idx : Nat) : Nat :=
  let p0 := 4 * idx
  if p0 + 3 < s.length then
    let c0 := s.get ⟨p0⟩
    let c1 := s.get ⟨p0 + 1⟩
    let c2 := s.get ⟨p0 + 2⟩
    let c3 := s.get ⟨p0 + 3⟩
    hex_char_val c0 * 4096 + hex_char_val c1 * 256 + hex_char_val c2 * 16 + hex_char_val c3
  else 0

#eval decode_witness "00010002000a" 0
#eval decode_witness "00010002000a" 1
#eval decode_witness "00010002000a" 2
