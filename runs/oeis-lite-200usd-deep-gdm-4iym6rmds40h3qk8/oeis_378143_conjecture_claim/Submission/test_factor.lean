import FormalConjectures.Util.ProblemImports

open Nat Set

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

-- A prime divisor of 10^(2^13)+1 is actually not needed if we prove compositeness of 10^(2^13)+1 by a prime factor we can compute!
-- Wait! Is there a prime factor of 10^(2^13)+1 that we can verify?
-- Actually, we don't need to find a prime factor of 10^(2^13)+1 if we can just prove that 10^(2^(m+13)) + 1 is composite by showing it has a factor, but wait!
-- Is there a known prime factor of 10^(2^13)+1?
-- Let's check if the C program found a factor!
