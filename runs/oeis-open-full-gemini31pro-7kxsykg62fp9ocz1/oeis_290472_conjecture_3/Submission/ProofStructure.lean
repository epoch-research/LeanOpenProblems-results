import Submission.Spec

def fast_sqrt (n : Nat) : Nat :=
  let rec loop (low high : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => low
    | f + 1 =>
      if low <= high then
        let mid := (low + high) >>> 1
        let sq := mid * mid
        if sq == n then mid
        else if sq < n then loop (mid + 1) high f
        else if mid == 0 then 0 else loop low (mid - 1) f
      else high
  loop 0 7746 14

def check_sol (N y z : Nat) : Bool :=
  if 3 * y * y + 7 * z * z < N then
    let rem := N - 3 * y * y - 7 * z * z
    let x := fast_sqrt rem
    x > 0 && x * x == rem
  else false

def verify_hint (N : Nat) (hint : Nat) : Bool :=
  let y1 := hint &&& 0x1FFF
  let z1 := (hint >>> 13) &&& 0x7F
  let y2 := (hint >>> 20) &&& 0x1FFF
  let z2 := (hint >>> 33) &&& 0x7F
  check_sol N y1 z1 && check_sol N y2 z2 &&
  (y1 != y2 || z1 != z2)

def verify_chunk (start_n : Nat) (chunk : Nat) : Bool :=
  let rec loop (i : Nat) (c : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => true
    | f + 1 => verify_hint (6 * (start_n + i) + 1) c && loop (i + 1) (c >>> 40) f
  loop 0 chunk 100

-- We need a dummy theorem to verify syntax
theorem dummy : True := trivial
