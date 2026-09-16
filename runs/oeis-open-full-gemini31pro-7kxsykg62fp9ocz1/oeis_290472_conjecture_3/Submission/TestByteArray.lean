def my_data : String := include_str "dummy.txt"

def test_char : Bool :=
  let b := my_data.toUTF8
  b.size == 10000000

theorem test : test_char = true := by decide
