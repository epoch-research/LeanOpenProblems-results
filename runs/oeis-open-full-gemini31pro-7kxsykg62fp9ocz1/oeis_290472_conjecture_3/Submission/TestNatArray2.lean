def my_nats : Array Nat := #[0x1234, 0x5678]

def test_arr : Bool :=
  my_nats[1]! == 0x5678

theorem test : test_arr = true := by decide
