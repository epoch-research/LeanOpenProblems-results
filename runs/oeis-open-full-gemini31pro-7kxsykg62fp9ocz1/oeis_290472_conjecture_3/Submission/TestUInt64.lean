set_option maxRecDepth 200000
def test_uint64 (n : UInt64) : Nat :=
  let rec loop (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i' + 1 =>
      let b := (n >>> (i' % 64).toUInt64) &&& 1
      loop i' (acc + b.toNat)
  loop 100000 0

theorem test : test_uint64 0x123456789ABCDEF0 = 50000 := by decide
