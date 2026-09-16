set_option maxRecDepth 200000
def my_str : String := include_str "dummy.txt"

def loop (i : Nat) : Nat :=
  match i with
  | 0 => 0
  | i' + 1 => loop i' + (String.Pos.Raw.get my_str ⟨90000⟩).toNat

theorem test : loop 2 = 132 := by decide
