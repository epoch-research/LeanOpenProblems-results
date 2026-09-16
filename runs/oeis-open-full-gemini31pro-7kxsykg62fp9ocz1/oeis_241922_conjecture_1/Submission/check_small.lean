import Submission.Spec

def check (n : ℕ) : Bool :=
  if n % 2 == 0 && n > 2 then
    List.any (List.range n) (fun p =>
      if p < 2 then false else
      if (List.range p).any (fun d => d > 1 && p % d == 0) then false else
      let q := n - p
      if q < 2 then false else
      if (List.range q).any (fun d => d > 1 && q % d == 0) then false else
      true
    )
  else true

#eval List.all (List.range 100) check
