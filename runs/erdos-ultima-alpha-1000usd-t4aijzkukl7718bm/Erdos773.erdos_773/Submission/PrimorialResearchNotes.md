# Primorial upper bound (still not a settlement)

`Spec.lean` now includes the verified lemma
`Erdos773.square_sidon_primorial_upper`:

For N >= 128^128,
M_N <= 2*N*exp(-log(N)/(512*log(log(N)))).

This is asymptotically stronger than the prior stretched-exponential upper
bound, but remains entirely compatible with the conjecture N^(1-o(1)).
The exponent loss is 1/(512 log log N), which tends to zero.

The lower bound remains N^(2/3-o(1)). The original theorem still has one sorry,
now at line 1515. Its statement and sole import were compared with the backup
and are unchanged. No submit_proof call has been made.

`PrimorialSquareSieve.lean` develops the bound independently, importing the
existing elementary modular sieve. The needed lemmas were consolidated into
Spec.lean without adding an import. `SpecStretchedUpperBackup.lean` is the
pre-consolidation backup. `Audit.lean` copies the main file and prints axioms of
the lower bound, density-zero bound, and new upper bound. Each prints exactly
[propext, Classical.choice, Quot.sound]. The main theorem remains admitted.

Proof:
1. 2^n <= centralBinom(n) <= (2n)^(number of primes <= 2n).
   The second inequality uses Nat.pow_factorization_choose_le.
2. Excluding primes 2 and 3 leaves k primes with k*log(n) >= n/8 for n>=128.
3. Their product Q is <= primorial(2n) <= 4^(2n), and their square-residue
   density is <= (3/4)^k by CRT.
4. Since k <= 3n, 2^k Q <= 128^n. The modular Sidon bound then gives
   M_N <= 2 (sqrt(3/4))^k N whenever 128^n <= N.
5. Set n = floor(log_128 N); elementary logarithmic estimates finish.

The proof adds an elementary prime-counting lower estimate without requiring
Chebyshev's lower bound as a separate imported theorem.
