def my_data : String := include_str "dummy.txt"

def test_char : Bool :=
  let r := my_data.foldl (fun acc c => if c == 'B' then acc + 1 else acc) 0
  r == 500000

theorem test : test_char = true := by decide
