import Mathlib

def a_fast_opt (n : UInt64) : Bool := Id.run do
  let N := 6 * n + 1
  let max_z := (N / 7).toFloat.sqrt.toUInt64
  let mut count := 0
  for z in [0:max_z.toNat + 1] do
    let z64 := z.toUInt64
    let rem1 := N - 7 * z64 * z64
    let max_y := (rem1 / 3).toFloat.sqrt.toUInt64
    for y in [0:max_y.toNat + 1] do
      let y64 := y.toUInt64
      let rem2 := rem1 - 3 * y64 * y64
      if rem1 > 3 * y64 * y64 then
        let x := rem2.toFloat.sqrt.toUInt64
        if x * x == rem2 then
          count := count + 1
          if count > 1 then return true
  return false

def main : IO Unit := do
  let mut all_ok := true
  for i in [287:1000000+1] do
    if !a_fast_opt i.toUInt64 then
      IO.println s!"Counterexample {i}"
      all_ok := false
      break
  if all_ok then IO.println "OK"
