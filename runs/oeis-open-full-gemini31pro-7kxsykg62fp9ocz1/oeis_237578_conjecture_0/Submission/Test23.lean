import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n ≤ 1 then false
  else if n ≤ 3 then true
  else if n % 2 == 0 ∨ n % 3 == 0 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i == 0 ∨ n % (i + 2) == 0 then false
      else loop (i + 6)
    loop 5

def primesUpTo (m : ℕ) : Array Bool :=
  Id.run do
    let mut arr := Array.mkArray (m + 1) true
    if m ≥ 0 then arr := arr.set! 0 false
    if m ≥ 1 then arr := arr.set! 1 false
    for i in [2:m+1] do
      if arr[i]! then
        let mut j := i * i
        while j ≤ m do
          arr := arr.set! j false
          j := j + i
    arr

def piArr (m : ℕ) : Array ℕ :=
  Id.run do
    let isP := primesUpTo m
    let mut arr := Array.mkArray (m + 1) 0
    let mut c := 0
    for i in [0:m+1] do
      if isP[i]! then c := c + 1
      arr := arr.set! i c
    arr

def a_fast (n : ℕ) (pi : Array ℕ) (isP : Array Bool) : ℕ :=
  let mut c := 0
  for k in [1:n] do
    let p := pi[k * n]!
    if isP[p]! then
      c := c + 1
  c

def check (max_n : ℕ) : Bool :=
  let m := max_n * max_n
  let isP := primesUpTo m
  let pi := piArr m
  let mut ok := true
  for n in [0:max_n] do
    let an := if n == 0 then 0 else a_fast n pi isP
    if 2 < n && an == 0 then ok := false
    let b1 := (an == 1)
    let b2 := (n == 5 || n == 8 || n == 13)
    if b1 != b2 then ok := false
  ok

#eval check 500
