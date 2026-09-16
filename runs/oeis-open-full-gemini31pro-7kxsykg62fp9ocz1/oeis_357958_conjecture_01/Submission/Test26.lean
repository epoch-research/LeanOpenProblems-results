import Submission.Spec

def check_primes (n : ℕ) : Bool :=
  let p_list := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
  p_list.all fun p => (a p) % p^5 == (a 1) % p^5

#eval check_primes 50
