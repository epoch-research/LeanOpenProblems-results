import Submission.Spec
open Nat List

def A321475_comp (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let noz (k : ℕ) : ℕ :=
      ofDigits 10 (filter (fun (d : ℕ) => decide (d ≠ 0)) (digits 10 k))
    let rec loop (i : ℕ) (P : ℕ) : ℕ :=
      if i = 0 then P
      else loop (i - 1) (noz (i * P))
    loop (n - 1) n

theorem A321475_eq_comp (n : ℕ) : A321475 n = A321475_comp n := by
  rfl
