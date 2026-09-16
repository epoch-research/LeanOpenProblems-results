import Mathlib

def build_sieve_inner (arr : Array ℕ) (p j : ℕ) (fuel : ℕ) : Array ℕ :=
  match fuel with
  | 0 => arr
  | f + 1 =>
    if j < arr.size then
      let arr_new := if arr[j]! == j then arr.set! j p else arr
      build_sieve_inner arr_new p (j + p) f
    else arr

def build_sieve_outer (arr : Array ℕ) (p : ℕ) (fuel : ℕ) : Array ℕ :=
  match fuel with
  | 0 => arr
  | f + 1 =>
    if p * p > arr.size then arr
    else
      let arr_new := if arr[p]! == p then build_sieve_inner arr p (p * p) (arr.size / p + 1) else arr
      build_sieve_outer arr_new (p + 1) f

def init_sieve (arr : Array ℕ) (i : ℕ) (fuel : ℕ) : Array ℕ :=
  match fuel with
  | 0 => arr
  | f + 1 =>
    if i < arr.size then init_sieve (arr.set! i i) (i + 1) f else arr

def build_sieve (limit : ℕ) : Array ℕ :=
  let arr := init_sieve (Array.mk (List.replicate limit 0)) 2 limit
  build_sieve_outer arr 2 limit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem test_sieve : (build_sieve 10000)[9999]! = 3 := by decide
