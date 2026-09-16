import Mathlib

def check_ap4 (n : ℕ) : Bool :=
  Id.run do
    for i in List.range (n + 1) do
      for j in List.range (n + 1) do
        for k in List.range (n + 1) do
          for l in List.range (n + 1) do
            if i < j && j < k && k < l then
              let a_coef := Nat.choose n i
              let b_coef := Nat.choose n j
              let c_coef := Nat.choose n k
              let d_coef := Nat.choose n l
              if 2 * b_coef == a_coef + c_coef && 2 * c_coef == b_coef + d_coef then
                return true
    return false

#eval (List.range 50).filter check_ap4
