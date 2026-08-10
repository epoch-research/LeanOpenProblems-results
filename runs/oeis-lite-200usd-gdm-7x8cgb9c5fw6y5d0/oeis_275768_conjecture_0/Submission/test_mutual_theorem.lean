import Mathlib

mutual
  theorem test1 (n : ℕ) : n = n := test2 n
  theorem test2 (n : ℕ) : n = n := test1 n
end
