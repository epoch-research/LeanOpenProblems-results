import Mathlib

def totient (n : ℕ) : ℕ :=
  let factors := n.primeFactorsList.eraseDups
  factors.foldl (fun acc p => acc * (p - 1) / p) n

def N_val (n : ℕ) := n.factorial

partial def search (N m : ℕ) : ℕ :=
  if totient m == N then m else search N (m + 1)

def A055487_comp (n : ℕ) : ℕ := search (N_val n) 1

def prime_candidates_comp (n : ℕ) : List ℕ :=
  let N := N_val n
  let sqrtN := Nat.sqrt N
  List.filter (fun p => p.Prime ∧ sqrtN < p ∧ (p - 1) ∣ N ∧ (N / (p - 1) + 1).Prime)
    (List.range (N + 1))

def formula (n : ℕ) : ℕ :=
  let N := N_val n
  let p := (prime_candidates_comp n).head!
  p * (N / (p - 1) + 1)

#eval A055487_comp 4 == formula 4
#eval A055487_comp 5 == formula 5
#eval A055487_comp 6 == formula 6
#eval A055487_comp 7 == formula 7
