import Submission.Spec

def b : ℕ := 38
def maxL : ℕ := 6

partial def dfs (k : ℕ) (delta : ℤ) (Pk : ℕ) : ℕ :=
  if k == maxL then 1
  else
    let bk := b ^ k
    if k > 0 && delta >= 0 && bk >= Pk * 37 then 1
    else
      let rec loop (d : ℕ) (acc : ℕ) : ℕ :=
        if d == b then acc
        else if k == 0 && d == 0 then loop (d + 1) acc
        else
          let n_delta := delta + (d * bk : ℤ) - ((d * d * Pk) : ℤ)
          let n_Pk := Pk * d
          loop (d + 1) (acc + dfs (k + 1) n_delta n_Pk)
      loop 0 0

def runTest : ℕ := dfs 0 0 1

#eval runTest
