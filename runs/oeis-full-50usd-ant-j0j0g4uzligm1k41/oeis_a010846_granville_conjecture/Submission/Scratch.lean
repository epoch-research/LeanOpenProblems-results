import FormalConjectures.Util.ProblemImports
open Nat Finset

example (p : ℕ) (hp : p.Prime) : p.primeFactors = {p} := hp.primeFactors
#check @Nat.exists_infinite_primes
#check @Nat.nonempty_primeFactors
#check @Nat.mem_primeFactors
#check @Real.exp_one_lt_d9
#check @Real.lt_log_iff_exp_lt
#check @Real.exp_nat_mul
#check @Real.rpow_lt_rpow
#check @Real.log_le_log
