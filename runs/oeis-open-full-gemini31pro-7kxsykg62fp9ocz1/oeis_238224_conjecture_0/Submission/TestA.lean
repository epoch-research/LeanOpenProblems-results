import Submission.Spec

def A238224_eval (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun j =>
    let upper_q : ℕ := (n - 1) / j
    Finset.sum (Finset.Icc 1 upper_q) fun q =>
      let k := j * q + 1
      if Nat.primeCounting (j * n) ∣ Nat.primeCounting (k * n) then 1 else 0

#eval A238224_eval 21
