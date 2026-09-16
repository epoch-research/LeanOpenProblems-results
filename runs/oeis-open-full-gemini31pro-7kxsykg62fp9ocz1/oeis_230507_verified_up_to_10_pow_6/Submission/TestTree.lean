def checkRange (start len : Nat) : Bool :=
  if h : len < 2 then
    if len = 1 then start < 10000000 else true
  else
    let half := len / 2
    have h1 : half < len := by omega
    have h2 : len - half < len := by omega
    checkRange start half && checkRange (start + half) (len - half)
termination_by len

theorem t1 : checkRange 0 1000000 = true := by decide
