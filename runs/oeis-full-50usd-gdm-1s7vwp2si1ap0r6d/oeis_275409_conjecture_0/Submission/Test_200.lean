import FormalConjectures.Util.ProblemImports


-- Wait, let's just define a_struct and proof_200 here
open Nat Finset

def sqrt_struct (n : ℕ) : ℕ :=
  if n < 4 then (if n < 1 then 0 else 1)
  else if n < 9 then 2
  else if n < 16 then 3
  else if n < 25 then 4
  else if n < 36 then 5
  else if n < 49 then 6
  else if n < 64 then 7
  else if n < 81 then 8
  else if n < 100 then 9
  else if n < 121 then 10
  else if n < 144 then 11
  else if n < 169 then 12
  else if n < 196 then 13
  else 14

def is_square_struct (n : ℕ) : Bool :=
  let s := sqrt_struct n
  s * s == n

def a_struct (n : ℕ) : ℕ :=
  let rec loop_y (w x : ℕ) (y : ℕ) (acc : ℕ) : ℕ :=
    match y with
    | 0 =>
      let rem := n - 2 * w^2 - x^2
      let z := sqrt_struct rem
      if z * z == rem then
        let lin_comb := w + x + 2 * 0 + 4 * z
        if is_square_struct lin_comb then acc + 1 else acc
      else acc
    | y' + 1 =>
      let rem := n - 2 * w^2 - x^2 - y^2
      let new_acc :=
        let z := sqrt_struct rem
        if z * z == rem then
          let lin_comb := w + x + 2 * y + 4 * z
          if is_square_struct lin_comb then acc + 1 else acc
        else acc
      loop_y w x y' new_acc

  let rec loop_x (w : ℕ) (x : ℕ) (acc : ℕ) : ℕ :=
    match x with
    | 0 =>
      let limit_y := sqrt_struct (n - 2 * w^2)
      loop_y w 0 limit_y acc
    | x' + 1 =>
      let limit_y := sqrt_struct (n - 2 * w^2 - x^2)
      let new_acc := loop_y w x limit_y acc
      loop_x w x' new_acc

  let rec loop_w (w : ℕ) (acc : ℕ) : ℕ :=
    match w with
    | 0 =>
      let limit_x := sqrt_struct n
      loop_x 0 limit_x acc
    | w' + 1 =>
      let limit_x := sqrt_struct (n - 2 * w^2)
      let new_acc := loop_x w limit_x acc
      loop_w w' new_acc

  let limit_w := sqrt_struct (n / 2)
  loop_w limit_w 0

def A275409_zero_set : Finset ℕ := {3, 10}
def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem proof_200_struct : ∀ n ≤ 200,
  (a_struct n > 0 ↔ n ∉ A275409_zero_set) ∧
  (a_struct n = 1 ↔ n ∈ A275409_one_set) := by
  decide
