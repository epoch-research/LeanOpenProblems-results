theorem acc_all (x : Nat) : Acc (fun _ _ => True) x :=
  Acc.intro x (fun y _ => acc_all y)
