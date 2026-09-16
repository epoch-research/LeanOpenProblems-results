import Submission.Spec

def check (n : ℕ) : Bool :=
  let r1 := (List.range (n + 1)).any fun a =>
              (List.range (n + 1)).any fun b =>
                let m := 2^a * 3^b
                if m ≤ n then (6 * (n - m) + 1).Prime else false
  let r2 := (List.range (n + 1)).any fun a =>
              (List.range (n + 1)).any fun b =>
                let m := 2^a * 3^b
                if m < n then (6 * (n - m) - 1).Prime else false
  r1 || r2

#eval (List.range 1000).filter (fun n => n > 1 && !check n)
