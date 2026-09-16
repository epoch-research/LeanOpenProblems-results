def sum_tail (n : Nat) (acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n' + 1 => sum_tail n' (acc + 1)

#reduce sum_tail 100000 0
