import FormalConjectures.Util.ProblemImports
open Nat Finset
#check Nat.sum_four_squares

def A308934 (n : ℕ) : ℕ :=
  let max_e2 := (Nat.log 2 n / 2) + 1
  let max_e3 := (Nat.log 3 n / 2) + 1
  let max_y := Nat.sqrt (n / 2)
  let r (k l : ℕ) : ℕ := (2^k * 3^l)
  let is_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m
  Finset.sum (range max_e2) fun a =>
    Finset.sum (range max_e3) fun b =>
      let r_val := r a b
      Finset.sum (range max_e2) fun c =>
        Finset.sum (range max_e3) fun d =>
          let s_val := r c d
          if r_val < s_val then 0 else
          if r_val^2 + s_val^2 > n then 0 else
          Finset.card $ Finset.filter (fun y =>
            let k := r_val^2 + s_val^2 + 2 * y^2
            k ≤ n ∧ is_square (n - k)
          ) (range (max_y + 1))
example (n : ℕ) (hn : n > 1) : A308934 n > 0 := by
  exact?
