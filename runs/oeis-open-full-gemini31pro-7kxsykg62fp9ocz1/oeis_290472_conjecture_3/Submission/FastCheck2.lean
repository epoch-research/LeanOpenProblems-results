set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def loop_y (N z : Nat) (y : Nat) (x : Nat) (acc : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let val := 3 * y * y + 7 * z * z
    if val > N then acc
    else
      let rem := N - val
      let rec drop_x (x : Nat) (x_fuel : Nat) : Nat :=
        match x_fuel with
        | 0 => x
        | xf + 1 => if x * x > rem then drop_x (x - 1) xf else x
      let nx := drop_x x x
      let is_match := if nx == 0 then false else (nx * nx == rem)
      let nacc := if is_match then acc + 1 else acc
      if nacc > 1 then nacc
      else loop_y N z (y + 1) nx nacc f

def loop_z (N : Nat) (z : Nat) (acc : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if 7 * z * z > N then acc
    else
      let rem := N - 7 * z * z
      let rec find_x (x : Nat) (x_fuel : Nat) : Nat :=
        match x_fuel with
        | 0 => x
        | xf + 1 =>
          if (x + 1) * (x + 1) <= rem then find_x (x + 1) xf else x
      -- find_x 0 rem is slow. better to start from a bound or just use a simple approx
      -- wait, x <= N is always true, so we can just drop_x from N
      let rec drop_x (x : Nat) (x_fuel : Nat) : Nat :=
        match x_fuel with
        | 0 => x
        | xf + 1 => if x * x > rem then drop_x (x - 1) xf else x
      let start_x := drop_x (N / 2 + 1) (N / 2 + 1)
      
      let y_fuel := N / 3 + 2
      let acc' := loop_y N z 0 start_x acc y_fuel
      if acc' > 1 then acc' else loop_z N (z + 1) acc' f

def count_sols (N : Nat) : Nat :=
  loop_z N 0 0 (N / 7 + 2)

def check_range (start len : Nat) : Bool :=
  match len with
  | 0 => true
  | l + 1 =>
    if count_sols (6 * start + 1) > 1 then
      check_range (start + 1) l
    else false

theorem test : check_range 287 4 = true := by decide
