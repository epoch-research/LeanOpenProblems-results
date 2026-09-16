import Mathlib

def build_array_tree (start len fuel : ℕ) (acc : Array ℕ) : Array ℕ :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    match len with
    | 0 => acc
    | 1 => acc.push start
    | _ =>
      let half := len / 2
      let acc' := build_array_tree start half f acc
      build_array_tree (start + half) (len - half) f acc'

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t : (build_array_tree 0 100000 100000 (Array.mkEmpty 100000)).size = 100000 := by decide
