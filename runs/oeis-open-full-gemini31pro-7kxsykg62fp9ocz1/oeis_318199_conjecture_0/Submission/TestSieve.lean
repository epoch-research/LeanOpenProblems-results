def sieve (limit : Nat) : Nat := Id.run do
  let mut arr : Array Bool := Array.mkArray limit true
  if limit > 0 then arr := arr.set! 0 false
  if limit > 1 then arr := arr.set! 1 false
  for p in [2:limit] do
    if p * p > limit then break
    if arr[p]! then
      let mut i := p * p
      while i < limit do
        arr := arr.set! i false
        i := i + p
  let mut count := 0
  for i in [0:limit] do
    if arr[i]! then
      count := count + 1
  return count

#eval! sieve 10000000
