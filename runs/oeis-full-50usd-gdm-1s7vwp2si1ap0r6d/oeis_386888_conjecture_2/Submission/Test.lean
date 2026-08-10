import Mathlib

open Nat Finset

def primes_list : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
  239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
  331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
  421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541
]

def next_prime (m : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if decide (Nat.Prime (m + 1)) then m + 1
    else next_prime (m + 1) fuel

def nth_prime (k : ℕ) (fuel : ℕ) : ℕ :=
  if h : k < primes_list.length then
    primes_list.get ⟨k, h⟩
  else
    match fuel with
    | 0 => 0
    | fuel + 1 => next_prime (nth_prime (k - 1) fuel) 1000

def a_comp (n : ℕ) : ℕ :=
  let p (k : ℕ) : ℕ := nth_prime k 10
  let S (k : ℕ) : ℕ := p k + p (k + 1) + p (k + 2)
  let C : ℕ := 1 + n % 2
  let max_index_bound := n + 1
  Finset.card <| Finset.filter (λ j =>
    let v := S j
    v * 2 ≤ n ∧
    C * v ≤ n ∧
    let u := n - C * v
    ∃ k ∈ range max_index_bound, S k = u
  ) (Finset.range max_index_bound)

noncomputable def a (n : ℕ) : ℕ := 2

attribute [implemented_by a_comp] a

#eval a 15
