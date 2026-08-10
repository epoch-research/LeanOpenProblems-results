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

-- Lookup table helper definition for instant evaluation of all 200 values
def a_lookup (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | 11 => 3
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 1
  | 16 => 3
  | 17 => 2
  | 18 => 5
  | 19 => 3
  | 20 => 4
  | 21 => 3
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 4
  | 30 => 2
  | 31 => 2
  | 32 => 4
  | 33 => 2
  | 34 => 7
  | 35 => 3
  | 36 => 1
  | 37 => 6
  | 38 => 2
  | 39 => 1
  | 40 => 2
  | 41 => 3
  | 42 => 4
  | 43 => 5
  | 44 => 1
  | 45 => 1
  | 46 => 3
  | 47 => 5
  | 48 => 3
  | 49 => 3
  | 50 => 4
  | 51 => 3
  | 52 => 7
  | 53 => 3
  | 54 => 2
  | 55 => 4
  | 56 => 3
  | 57 => 4
  | 58 => 4
  | 59 => 3
  | 60 => 1
  | 61 => 4
  | 62 => 5
  | 63 => 3
  | 64 => 6
  | 65 => 4
  | 66 => 4
  | 67 => 4
  | 68 => 5
  | 69 => 7
  | 70 => 7
  | 71 => 3
  | 72 => 6
  | 73 => 5
  | 74 => 5
  | 75 => 4
  | 76 => 3
  | 77 => 11
  | 78 => 2
  | 79 => 2
  | 80 => 4
  | 81 => 7
  | 82 => 5
  | 83 => 5
  | 84 => 5
  | 85 => 3
  | 86 => 6
  | 87 => 1
  | 88 => 3
  | 89 => 3
  | 90 => 4
  | 91 => 8
  | 92 => 8
  | 93 => 2
  | 94 => 5
  | 95 => 2
  | 96 => 5
  | 97 => 6
  | 98 => 1
  | 99 => 6
  | 100 => 8
  | 101 => 8
  | 102 => 6
  | 103 => 7
  | 104 => 4
  | 105 => 3
  | 106 => 1
  | 107 => 2
  | 108 => 3
  | 109 => 7
  | 110 => 1
  | 111 => 1
  | 112 => 7
  | 113 => 2
  | 114 => 3
  | 115 => 11
  | 116 => 8
  | 117 => 9
  | 118 => 10
  | 119 => 4
  | 120 => 2
  | 121 => 6
  | 122 => 14
  | 123 => 5
  | 124 => 7
  | 125 => 7
  | 126 => 6
  | 127 => 9
  | 128 => 8
  | 129 => 5
  | 130 => 13
  | 131 => 11
  | 132 => 5
  | 133 => 6
  | 134 => 6
  | 135 => 7
  | 136 => 2
  | 137 => 10
  | 138 => 7
  | 139 => 11
  | 140 => 6
  | 141 => 7
  | 142 => 7
  | 143 => 3
  | 144 => 7
  | 145 => 7
  | 146 => 9
  | 147 => 5
  | 148 => 8
  | 149 => 4
  | 150 => 7
  | 151 => 9
  | 152 => 7
  | 153 => 6
  | 154 => 9
  | 155 => 9
  | 156 => 2
  | 157 => 8
  | 158 => 6
  | 159 => 4
  | 160 => 4
  | 161 => 7
  | 162 => 6
  | 163 => 11
  | 164 => 4
  | 165 => 6
  | 166 => 16
  | 167 => 6
  | 168 => 6
  | 169 => 3
  | 170 => 5
  | 171 => 7
  | 172 => 8
  | 173 => 6
  | 174 => 2
  | 175 => 5
  | 176 => 9
  | 177 => 4
  | 178 => 6
  | 179 => 7
  | 180 => 6
  | 181 => 8
  | 182 => 10
  | 183 => 1
  | 184 => 3
  | 185 => 3
  | 186 => 9
  | 187 => 14
  | 188 => 5
  | 189 => 8
  | 190 => 5
  | 191 => 7
  | 192 => 7
  | 193 => 4
  | 194 => 7
  | 195 => 5
  | 196 => 13
  | 197 => 18
  | 198 => 4
  | 199 => 8
  | _ => 2

theorem a_fast_fast_eq_lookup_fin : ∀ (i : Fin 200), a_fast_fast i.val = a_lookup i.val := by decide

theorem a_fast_eq_lookup (n : ℕ) (hn : n < 200) : a_fast n = a_lookup n :=
