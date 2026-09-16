import Submission.Spec
open Nat Finset

def check_all : Bool :=
  let s := [0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534]
  s.all (fun n => A271099 n == 1)

def main : IO Unit := do
  IO.println check_all
