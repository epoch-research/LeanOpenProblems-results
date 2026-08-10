import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000

def f_seq (M : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun x => x ^ 10 % M
  | i + 1 => fun x =>
      let f := f_seq M i
      f (f x)

def M_val : ℕ := 10 ^ (2 ^ 21) + 1

#eval (f_seq M_val 21 3) % 10
