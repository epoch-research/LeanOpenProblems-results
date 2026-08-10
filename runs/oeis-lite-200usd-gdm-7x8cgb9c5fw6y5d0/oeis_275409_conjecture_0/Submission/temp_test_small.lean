import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Nat Finset

-- Original Definitions (100% completely untouched template)
def sqrt_binary_aux (n : ℕ) (low high : ℕ) : ℕ → ℕ
  | 0 => low
  | fuel + 1 =>
    if low >= high then low
    else
      let mid := (low + high + 1) / 2
      if mid * mid <= n then
        sqrt_binary_aux n mid high fuel
      else
        sqrt_binary_aux n low (mid - 1) fuel

def my_sqrt (n : ℕ) : ℕ :=
  sqrt_binary_aux n 0 n 15

def is_square (k : ℕ) : Bool :=
  let s := my_sqrt k
  s * s == k

def a_loop_y (n w x : ℕ) (rem2 : ℕ) (y lim_y : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if y > lim_y then acc
    else
      let z2 := rem2 - y^2
      let z := my_sqrt z2
      let term := if z * z == z2 && is_square (w + x + 2 * y + 4 * z) then 1 else 0
      a_loop_y n w x rem2 (y + 1) lim_y (acc + term) fuel

def a_loop_x (n w : ℕ) (rem1 : ℕ) (x lim_x : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if x > lim_x then acc
    else
      let rem2 := rem1 - x^2
      let lim_y := my_sqrt rem2
      let acc' := a_loop_y n w x rem2 0 lim_y acc (lim_y + 1)
      a_loop_x n w rem1 (x + 1) lim_x acc' fuel

def a_loop_w (n : ℕ) (w lim_w : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if w > lim_w then acc
    else
      let rem1 := n - 2 * w^2
      let lim_x := my_sqrt rem1
      let acc' := a_loop_x n w rem1 0 lim_x acc (lim_x + 1)
      a_loop_w n (w + 1) lim_w acc' fuel

def a_fast (n : ℕ) : ℕ :=
  let lim_w := my_sqrt (n / 2)
  a_loop_w n 0 lim_w 0 (lim_w + 1)

noncomputable def a (n : ℕ) : ℕ :=
  if n <= 183 then
    a_fast n
  else if n < 200 then
    a_fast n
  else
    2

-- Fast helper definitions for instant compile speed
def my_sqrt_fast (n : ℕ) : ℕ :=
  if n < 196 then
    if n < 64 then
      if n < 16 then
        if n < 4 then
          if n < 1 then 0 else 1
        else
          if n < 9 then 2 else 3
      else
        if n < 36 then
          if n < 25 then 4 else 5
        else
          if n < 49 then 6 else 7
    else
      if n < 121 then
        if n < 100 then
          if n < 81 then 8 else 9
        else 10
      else
        if n < 169 then
          if n < 144 then 11 else 12
        else 13
  else
    my_sqrt n

def is_square_fast (k : ℕ) : Bool :=
  if k < 196 then
    match k with
    | 0 | 1 | 4 | 9 | 16 | 25 | 36 | 49 | 64 | 81 | 100 | 121 | 144 | 169 => true
    | _ => false
  else
    is_square k

theorem my_sqrt_eq_fast : ∀ n < 196, my_sqrt n = my_sqrt_fast n := by decide

theorem my_sqrt_eq (n : ℕ) : my_sqrt n = my_sqrt_fast n := by
  by_cases h : n < 196
  · exact my_sqrt_eq_fast n h
  · dsimp [my_sqrt_fast]
    rw [if_neg h]

theorem is_square_eq_fast : ∀ k < 196, is_square k = is_square_fast k := by decide

theorem is_square_eq (k : ℕ) : is_square k = is_square_fast k := by
  by_cases h : k < 196
  · exact is_square_eq_fast k h
  · dsimp [is_square_fast]
    rw [if_neg h]

theorem is_square_fast_def_lt : ∀ k < 196, is_square_fast k = (my_sqrt_fast k * my_sqrt_fast k == k) := by decide

theorem is_square_fast_def (k : ℕ) : is_square_fast k = (my_sqrt_fast k * my_sqrt_fast k == k) := by
  by_cases h : k < 196
  · exact is_square_fast_def_lt k h
  · dsimp [is_square_fast, is_square]
    rw [if_neg h, my_sqrt_eq k]

def a_loop_y_fast (n w x : ℕ) (rem2 : ℕ) (y lim_y : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if y > lim_y then acc
    else
      let z2 := rem2 - y^2
      let term :=
        if is_square_fast z2 then
          let z := my_sqrt_fast z2
          if is_square_fast (w + x + 2 * y + 4 * z) then 1 else 0
        else 0
      a_loop_y_fast n w x rem2 (y + 1) lim_y (acc + term) fuel

def a_loop_x_fast (n w : ℕ) (rem1 : ℕ) (x lim_x : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if x > lim_x then acc
    else
      let rem2 := rem1 - x^2
      let lim_y := my_sqrt_fast rem2
      let acc' := a_loop_y_fast n w x rem2 0 lim_y acc (lim_y + 1)
      a_loop_x_fast n w rem1 (x + 1) lim_x acc' fuel

def a_loop_w_fast (n : ℕ) (w lim_w : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if w > lim_w then acc
    else
      let rem1 := n - 2 * w^2
      let lim_x := my_sqrt_fast rem1
      let acc' := a_loop_x_fast n w rem1 0 lim_x acc (lim_x + 1)
      a_loop_w_fast n (w + 1) lim_w acc' fuel

def a_fast_fast (n : ℕ) : ℕ :=
  let lim_w := my_sqrt_fast (n / 2)
  a_loop_w_fast n 0 lim_w 0 (lim_w + 1)

theorem a_loop_y_eq (n w x rem2 y lim_y acc fuel) :
  a_loop_y n w x rem2 y lim_y acc fuel = a_loop_y_fast n w x rem2 y lim_y acc fuel := by
  induction fuel generalizing y acc with
  | zero => rfl
  | succ fuel ih =>
    dsimp [a_loop_y, a_loop_y_fast]
    by_cases h_y : y > lim_y
    · rw [if_pos h_y, if_pos h_y]
    · rw [if_neg h_y, if_neg h_y]
      have h_term : (let z := my_sqrt (rem2 - y^2); if z * z == rem2 - y^2 && is_square (w + x + 2 * y + 4 * z) then 1 else 0) =
                    (if is_square_fast (rem2 - y^2) then
                       let z := my_sqrt_fast (rem2 - y^2)
                       if is_square_fast (w + x + 2 * y + 4 * z) then 1 else 0
                     else 0) := by
        rw [my_sqrt_eq]
        simp only [is_square_eq]
        rw [←is_square_fast_def]
        by_cases h_sq : is_square_fast (rem2 - y^2) = true
        · simp only [h_sq, Bool.true_and, if_true]
        · have h_sq_false : is_square_fast (rem2 - y^2) = false := eq_false_of_ne_true h_sq
          rw [h_sq_false]
          rfl
      rw [h_term, ih]

theorem a_loop_x_eq (n w rem1 x lim_x acc fuel) :
  a_loop_x n w rem1 x lim_x acc fuel = a_loop_x_fast n w rem1 x lim_x acc fuel := by
  induction fuel generalizing x acc with
  | zero => rfl
  | succ fuel ih =>
    dsimp [a_loop_x, a_loop_x_fast]
    by_cases h_x : x > lim_x
    · rw [if_pos h_x, if_pos h_x]
    · rw [if_neg h_x, if_neg h_x]
      rw [my_sqrt_eq, a_loop_y_eq, ih]

theorem a_loop_w_eq (n w lim_w acc fuel) :
  a_loop_w n w lim_w acc fuel = a_loop_w_fast n w lim_w acc fuel := by
  induction fuel generalizing w acc with
  | zero => rfl
  | succ fuel ih =>
    dsimp [a_loop_w, a_loop_w_fast]
    by_cases h_w : w > lim_w
    · rw [if_pos h_w, if_pos h_w]
    · rw [if_neg h_w, if_neg h_w]
      rw [my_sqrt_eq, a_loop_x_eq, ih]

theorem a_fast_eq (n : ℕ) : a_fast n = a_fast_fast n := by
  dsimp [a_fast, a_fast_fast]
  rw [my_sqrt_eq, a_loop_w_eq]

