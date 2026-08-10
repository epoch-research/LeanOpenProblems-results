import FormalConjectures.Util.ProblemImports

def hex_to_val (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parse_hex_list : List Char → List Nat
  | [] => []
  | _ :: [] => []
  | c1 :: c2 :: cs =>
    let val := hex_to_val c1 * 16 + hex_to_val c2
    val :: parse_hex_list cs

-- Let us define a small list of 4 bytes: "01020304"
def my_array : List Nat := parse_hex_list ['0', '1', '0', '2', '0', '3', '0', '4']

theorem test_decide : my_array.get! 2 = 3 := by
  decide
