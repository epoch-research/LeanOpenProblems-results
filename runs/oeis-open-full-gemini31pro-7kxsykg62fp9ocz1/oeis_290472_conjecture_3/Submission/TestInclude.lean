def my_data : String := include_str "dummy.txt"

def test_char : Bool :=
  my_data.get! ⟨5000000⟩ == 'B'

theorem test : test_char = true := by decide
