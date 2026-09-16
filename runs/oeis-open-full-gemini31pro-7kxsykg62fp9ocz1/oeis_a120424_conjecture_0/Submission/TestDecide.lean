def check_tiny : Bool :=
  Id.run do
    let mut arr := Array.mkArray 10 0
    for i in [0:10] do
      arr := arr.set! i i
    return arr[5]! == 5

theorem tiny_ok : check_tiny = true := by decide
