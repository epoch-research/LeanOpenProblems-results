import FormalConjectures.Util.ProblemImports

def my_str : String := "Hello"

def my_bytes : ByteArray := my_str.toUTF8

theorem test_bytes : my_bytes[1]! = 101 := by
  decide
