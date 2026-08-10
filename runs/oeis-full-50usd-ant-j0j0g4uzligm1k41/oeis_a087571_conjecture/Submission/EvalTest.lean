import FormalConjectures.Util.ProblemImports
open Nat
noncomputable def a (n : ℕ) : ℕ :=
  let get_all_digits_msf (L : List ℕ) : List ℕ :=
    let to_digits_msb (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse
    List.foldr (fun num acc_digits => (to_digits_msb num) ++ acc_digits) [] L
  let of_msb_digits (D : List ℕ) : ℕ :=
    D.foldl (fun acc d => acc * 10 + d) 0
  let concatenated_number (k : ℕ) : ℕ :=
    let num_list : List ℕ := List.map (fun i => n - i) (List.range (k + 1))
    of_msb_digits (get_all_digits_msf num_list)
  let candidates : List ℕ :=
    List.map concatenated_number (List.range n)
  match List.find? Nat.Prime candidates with
  | some p => p
  | none   => 0
#eval a 4
#eval a 10
#eval a 6
#eval a 22
