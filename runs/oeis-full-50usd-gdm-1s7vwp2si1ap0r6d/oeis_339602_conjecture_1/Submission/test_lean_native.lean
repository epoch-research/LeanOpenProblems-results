def A030101_fast (n : Nat) : Nat :=
  let rec loop (n rev : Nat) : Nat :=
    if n = 0 then rev
    else loop (n / 2) (rev * 2 + n % 2)
  loop n 0

def a_step (acc : Nat × Nat) : Nat × Nat :=
  (acc.2, acc.1.xor (A030101_fast acc.2) + 1)

def a_aux_iter : Nat → Nat × Nat → Nat × Nat
  | 0, acc => acc
  | n + 1, acc => a_aux_iter n (a_step acc)

def main : IO Unit := do
  let N := 3412541655
  let res := (a_aux_iter N (0, 1)).1
  IO.println s!"a({N}) = {res}"

