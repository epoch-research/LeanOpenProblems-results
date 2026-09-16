set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def my_sqrt (n : Nat) : Nat :=
  let rec loop (x : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => x
    | f + 1 =>
      let nx := (x + n / x) / 2
      if nx < x then loop nx f else x
  if n <= 1 then n else loop n n

def loop_y (N z : Nat) (y : Nat) (acc : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if 3 * y * y + 7 * z * z > N then acc
    else
      let rem := N - 3 * y * y - 7 * z * z
      if rem == 0 then loop_y N z (y + 1) acc f
      else
        let r := my_sqrt rem
        if r * r == rem then loop_y N z (y + 1) (acc + 1) f
        else loop_y N z (y + 1) acc f

def loop_z (N : Nat) (z : Nat) (acc : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if 7 * z * z > N then acc
    else
      let y_fuel := N + 1
      let acc' := loop_y N z 0 acc y_fuel
      loop_z N (z + 1) acc' f

def count_sols (N : Nat) : Nat :=
  loop_z N 0 0 (N + 1)

def check_range (start len : Nat) : Bool :=
  match len with
  | 0 => true
  | l + 1 =>
    if count_sols (6 * start + 1) > 1 then
      check_range (start + 1) l
    else false

theorem test : check_range 287 4 = true := by decide
