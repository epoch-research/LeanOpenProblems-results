import FormalConjectures.Util.ProblemImports

open Nat List Finset

def chi_P (k : ℕ) : ℕ := if k.Prime then 1 else 0

def list_dot_product (xs ys : List ℕ) : ℕ :=
  (xs.zipWith (fun a b => a * b) ys).sum

def b_vec (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => chi_P (i.val + 1))

def cyclic_autocorrelation (n j : ℕ) : ℕ :=
  let b_n := b_vec n
  list_dot_product b_n (b_n.rotate (n - j))

noncomputable def A338238 (n : ℕ) : ℕ :=
  if h_n : n ≥ 2 then
    let rotations : List ℕ := (List.range n).tail
    let M : ℕ := (rotations.map (cyclic_autocorrelation n)).maximum.getD 0
    rotations.find? (fun j => cyclic_autocorrelation n j = M) |>.getD 0
  else
    1

noncomputable def Nat_primorial (n : ℕ) : ℕ := (Finset.filter (fun p => p.Prime) (Finset.range (n + 1))).prod id

theorem A338238_infinitely_often_primorial_conjecture :
  Set.Infinite { val : ℕ | (∃ (n : ℕ), n ≥ 2 ∧ val = A338238 n) ∧ (∃ (m : ℕ), val = Nat_primorial m) } :=
  by sorry

theorem A338238_infinitely_often_primorial_conjecture.disproof : ¬ (type_of% @A338238_infinitely_often_primorial_conjecture) :=
  by sorry
