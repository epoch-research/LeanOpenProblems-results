def sum_fold (n : Nat) : Nat :=
  (List.range n).foldl (fun acc _ => acc + 1) 0

#reduce sum_fold 100000
