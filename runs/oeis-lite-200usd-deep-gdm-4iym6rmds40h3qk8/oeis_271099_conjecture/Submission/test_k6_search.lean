import FormalConjectures.Util.ProblemImports

open Nat Finset

def loop_dec (fuel : ℕ) (x : ℕ) (min_x : ℕ) (f : ℕ → List (List ℕ)) : List (List ℕ) :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if x < min_x then []
    else
      f x ++ loop_dec fuel' (x - 1) min_x f

def generate_complete_rec (rem_len : ℕ) (current_sum : ℕ) (last_val : ℕ) : List (List ℕ) :=
  match rem_len with
  | 0 => if current_sum = 73 then [[]] else []
  | r + 1 =>
    let idx := 11 - rem_len
    let min_x := if idx > 0 then last_val else 1
    let rem_sum := 73 - current_sum
    if rem_sum < rem_len * min_x then []
    else
      let max_x := min (current_sum + 1) (rem_sum / rem_len)
      let f := fun x =>
        let rest := generate_complete_rec r (current_sum + x) x
        rest.map (fun l => x :: l)
      loop_dec (max_x + 1) max_x min_x f

def get_val (dp : List Bool) (idx : ℕ) : Bool :=
  dp.getD idx false

def dp_step (coeff : ℕ) (dp : List Bool) : List Bool :=
  let t1 := coeff
  let t2 := 64 * coeff
  let t3 := 729 * coeff
  List.ofFn (fun (i : Fin 1401) =>
    let val : ℕ := i.val
    get_val dp val ||
    (if val ≥ t1 then get_val dp (val - t1) else false) ||
    (if val ≥ t2 then get_val dp (val - t2) else false) ||
    (if val ≥ t3 then get_val dp (val - t3) else false)
  )

def init_dp : List Bool :=
  True :: List.replicate 1400 False

def run_dp (c : List ℕ) : List Bool :=
  c.foldr dp_step init_dp

def is_working (c : List ℕ) : Bool :=
  (run_dp c).all (fun b => b)

#eval is_working [1, 1, 1, 1, 1, 2, 4, 6, 9, 15, 32]

def any_working : Bool :=
  (generate_complete_rec 11 0 1).any is_working

#eval any_working



#eval (generate_complete_rec 11 0 1).length
