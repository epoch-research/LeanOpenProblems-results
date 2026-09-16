import Mathlib

open Nat

def p_n (k : ℕ) : ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307].getD (k - 1) 0

def my_a (n : ℕ) : ℕ := (p_n n * p_n (n + 1)) % p_n (n + 2)

#eval my_a 1
#eval my_a 2
#eval my_a 3
#eval my_a 4
#eval my_a 5
#eval my_a 6
#eval my_a 7
#eval my_a 8
#eval my_a 9
#eval my_a 10
#eval my_a 11
#eval my_a 12
#eval my_a 13
#eval my_a 14
#eval my_a 15
#eval my_a 60
#eval my_a 61
