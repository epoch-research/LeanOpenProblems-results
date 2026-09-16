def my_data : String := include_str "dummy.txt"

def check_tree (s : String) (start depth : Nat) : Bool :=
  match depth with
  | 0 => String.Pos.Raw.get s ⟨start⟩ == 'B'
  | d + 1 =>
    let half := 1 <<< d
    check_tree s start d && check_tree s (start + half) d

def test_char : Bool :=
  check_tree my_data 0 22

theorem test : test_char = true := by decide
