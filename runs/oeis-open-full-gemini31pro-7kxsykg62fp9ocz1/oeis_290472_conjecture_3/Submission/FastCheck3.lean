set_option maxRecDepth 2000000

def my_sqrt (n : Nat) : Nat :=
  let rec loop (x : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => x
    | f + 1 =>
      let nx := (x + n / x) / 2
      if nx < x then loop nx f else x
  if n <= 1 then n else loop n 20

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
      let start_x := my_sqrt (N - 7 * z * z)
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

theorem test : check_range 287 10 = true := by decide
