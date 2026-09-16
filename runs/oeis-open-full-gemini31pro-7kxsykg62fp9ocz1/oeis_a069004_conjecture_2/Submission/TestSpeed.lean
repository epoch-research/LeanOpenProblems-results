import Mathlib

def main : IO Unit := do
  let start ← IO.monoMsNow
  let mut count := 0
  for s in [1:512720] do
    let p := 512720*512720 + s*s
    if Nat.minFac p == p then
      count := count + 1
  let stop ← IO.monoMsNow
  IO.println s!"count = {count}, time = {stop - start} ms"
