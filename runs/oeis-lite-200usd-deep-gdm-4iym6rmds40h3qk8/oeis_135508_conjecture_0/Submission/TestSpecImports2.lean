def x_seq_loop : Nat → Nat → Nat → Nat
| 0, _, x => x
| n + 1, i, x => x_seq_loop n (i + 1) (2 * x + Nat.lcm x i)

def x_seq_tr (n : Nat) : Nat :=
  if n = 0 then 0
  else x_seq_loop (n - 1) 2 1

lemma test : x_seq_tr 317 = x_seq_loop 316 2 1 := rfl
