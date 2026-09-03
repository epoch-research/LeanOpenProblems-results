import Submission.MixedPatternRescaling

def fastWheel (ps : List ℕ) (a m : ℕ) : ℕ :=
  ((List.range m).filter (fun i => ps.all (fun p => (a + i) % p != 0))).length

def fastCheck : Bool :=
  (List.range (3*11*17)).all (fun a => 38 ≤ fastWheel [3,11,17] a 69) &&
  (List.range (3*5*17)).all (fun a => 33 ≤ fastWheel [3,5,17] a 69) &&
  (List.range (3*5*11)).all (fun a => 32 ≤ fastWheel [3,5,11] a 69) &&
  (List.range 3).all (fun a => fastWheel [3] a 69 ≤ 46)

example : fastCheck = true := by decide +kernel
