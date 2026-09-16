import Submission.Spec

def check_C_pair (k m n : ℕ) : Bool :=
  let b := (List.range (n + 1)).any fun x =>
    (List.range (n + 1)).any fun y =>
      (List.range (2 * n + 2)).any fun z' =>
        let z : ℤ := if z' % 2 == 0 then (z' / 2 : ℕ) else -((z' / 2 + 1) : ℕ)
        P_k_first k x + P_k_second k y + (polygonal_num_val m z).toNat == n
  b

#eval! check_C_pair 5 7 0
#eval! check_C_pair 5 7 1
#eval! check_C_pair 5 7 2
#eval! check_C_pair 5 7 3
#eval! check_C_pair 5 7 4
#eval! check_C_pair 5 7 5
#eval! check_C_pair 5 7 6
#eval! check_C_pair 5 7 7
#eval! check_C_pair 5 7 8
#eval! check_C_pair 5 7 9
#eval! check_C_pair 5 7 10
#eval! check_C_pair 5 7 11
#eval! check_C_pair 5 7 12
#eval! check_C_pair 5 7 13
#eval! check_C_pair 5 7 14
#eval! check_C_pair 5 7 15
