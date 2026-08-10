import FormalConjectures.Util.ProblemImports

def hex_to_val (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parse_hex_aux (s : String) (i : Nat) (acc : ByteArray) : ByteArray :=
  if h : i < s.length then
    let c1 := s.get ⟨i⟩
    if h2 : i + 1 < s.length then
      let c2 := s.get ⟨i + 1⟩
      let val := hex_to_val c1 * 16 + hex_to_val c2
      parse_hex_aux s (i + 2) (acc.push val.toUInt8)
    else
      acc
  else
    acc
  termination_by s.length - i

def parse_hex (s : String) : ByteArray :=
  parse_hex_aux s 0 ByteArray.empty

-- Let us define a small hex string of 4 bytes: "01020304"
def my_array : ByteArray := parse_hex "01020304"

theorem test_decide : my_array.get! 2 = 3 := by
  decide
