set_option maxRecDepth 200000

def mk_array (depth : Nat) : ByteArray :=
  match depth with
  | 0 => ByteArray.mk #[1, 2, 3, 4]
  | d + 1 =>
    let arr := mk_array d
    arr ++ arr

theorem test : (mk_array 20).size = 4194304 := by decide
