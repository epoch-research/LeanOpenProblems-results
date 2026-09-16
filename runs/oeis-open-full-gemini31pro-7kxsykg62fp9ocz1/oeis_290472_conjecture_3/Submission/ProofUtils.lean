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

def check_chunk (start_n : Nat) (cases : Nat) (chunk : Nat) : Bool :=
  let rec loop (i : Nat) (c : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => true
    | f + 1 =>
      if i >= cases then true
      else
        let y1 := c &&& 0x1FFF
        let z1 := (c >>> 13) &&& 0x7F
        let y2 := (c >>> 20) &&& 0x1FFF
        let z2 := (c >>> 33) &&& 0x7F
        let N := 6 * (start_n + i) + 1
        let v1 := 3 * y1 * y1 + 7 * z1 * z1
        let v2 := 3 * y2 * y2 + 7 * z2 * z2
        if v1 < N && v2 < N then
          let rem1 := N - v1
          let rem2 := N - v2
          let x1 := fast_sqrt rem1
          let x2 := fast_sqrt rem2
          if x1 > 0 && x2 > 0 && x1 * x1 == rem1 && x2 * x2 == rem2 && (y1 != y2 || z1 != z2) then
            loop (i + 1) (c >>> 40) f
          else false
        else false
  loop 0 chunk 100
