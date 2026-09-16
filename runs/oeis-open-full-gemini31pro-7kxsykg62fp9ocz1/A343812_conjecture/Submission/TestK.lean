import Mathlib
open Nat Finset

def primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
   31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
   179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
   233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
   283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
   353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
   419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
   467, 479, 487, 491, 499, 503, 509, 521, 523, 541]

def p (i : ℕ) : ℕ := primes.getD i 0
def S (n : ℕ) : ℕ := (range n).sum p
def a_comp (n : ℕ) : ℕ := (range n).sum (fun i => S n % p i)

def find_collision : Option (ℕ × ℕ) :=
  let l := (List.range 100).filter (fun n => n > 0)
  let pairs := l.bind (fun m => l.map (fun n => (m, n)))
  pairs.find? (fun ⟨m, n⟩ => m < n ∧ a_comp m = a_comp n)

#eval find_collision
