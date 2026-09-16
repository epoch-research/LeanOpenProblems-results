import FormalConjectures.Util.ProblemImports

def primes : Array ℕ :=
  #[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
    73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173]

def isPrime (n : ℕ) : Bool :=
  primes.contains n

def comp_A236097 (n : ℕ) : ℕ := Id.run do
  let mut sum := 0
  for k in [1:n-2] do
    let p_val := Nat.totient k + Nat.totient (n - k) / 2 + 1
    let p_prime := if p_val - 1 < primes.size then primes[p_val - 1]! else 0
    if isPrime p_val && isPrime (p_prime - p_val - 1) && isPrime (p_prime - p_val + 1) then
      sum := sum + 1
  return sum

#eval! comp_A236097 32
#eval! comp_A236097 33
#eval! comp_A236097 34
