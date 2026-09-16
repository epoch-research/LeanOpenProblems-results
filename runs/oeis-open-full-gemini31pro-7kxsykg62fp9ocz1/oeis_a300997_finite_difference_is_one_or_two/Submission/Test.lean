import Submission.Spec
open List Nat Function Set

def a_test (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor
    let next_config_long := List.zipWith Nat.add base_masses received_masses
    trim_trailing_zeros next_config_long
  if n = 0 then 0 else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1
    let rec loop (config : List ℕ) (steps : ℕ) : ℕ :=
      if config = target_config then steps
      else if steps > 200 then 0
      else loop (ca_step config) (steps + 1)
    loop initial_config 0
  termination_by loop config steps => 200 - steps

#eval! a_test 1
#eval! a_test 2
#eval! a_test 3
#eval! a_test 4
