import Submission.Spec
open OeisA230507

def S_comp (m : ℕ) : Bool :=
  (Nat.minFac (2 * m + 1) == 2 * m + 1) && (2 * m + 1 > 1) &&
  (Nat.minFac (2 * m ^ 3 + 1) == 2 * m ^ 3 + 1) && (2 * m ^ 3 + 1 > 1)

def A_comp (n : ℕ) : Bool :=
  let rec loop_a (a : ℕ) : Bool :=
    if a > n / 3 then false
    else
      let rec loop_b (b : ℕ) : Bool :=
        if b > (n - a) / 2 then false
        else
          let c := n - a - b
          if S_comp a && S_comp b && S_comp c then true
          else loop_b (b + 1)
      if loop_b a then true
      else loop_a (a + 1)
  loop_a 1

#eval A_comp 100
