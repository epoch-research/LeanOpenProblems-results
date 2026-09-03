# Actual squarefree-support bound — original conjecture unresolved

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No complete proof or irrational counterexample has been obtained.

## New verified file

`Submission/SquarefreePrimeOutputBound.lean`
Namespace `Erdos972SquarefreePrimeOutputBound`.

### Finite support estimate

The Möbius function vanishes on multiples of 4 or 9. Inclusion-exclusion gives

    |mu(n)| <= 1 - 1_{4|n} - 1_{9|n} + 1_{36|n}.

For any nonnegative weight a on a finite input set S, this yields an upper
bound for both sum a(n)|mu(n)| and |sum a(n)mu(n)| by the corresponding
combination of divisor rows. If the four rows at 1,4,9,36 have error at most
E relative to X/d, then

    |sum a(n)mu(n)| <= (2/3)X + 4E.

The coefficient is exactly (1-1/4)(1-1/9)=2/3.

### Actual centered rows

`exists_small_centered_output_rows` strengthens the presentation of the
existing fixed-finite-divisor scale result: for every irrational alpha>1,
eta>0 and finite M,B, there is N>B such that, for every 0<d<=M,

    |sum_{n<=N,d|n} Lambda(floor(alpha*n)) - N/d| <= eta*N.

The common Chebyshev center is replaced by N using the already proved PNT.
The proof retains the actual row error and makes a common good-scale choice;
no new distribution hypothesis is imposed.

### Actual Möbius-output bound

`exists_moebius_output_support_bound` proves that for every irrational
alpha>1, epsilon>0 and B there is N>B with

    |sum_{n<=N} mu(n) Lambda(floor(alpha*n))| <= (2/3+epsilon)N.

This is an unconditional selected-scale SUPPORT bound. It is not o(N)
cancellation, nor is it a lower bound for the prime-input Mangoldt correlation.
It therefore does not settle the conjecture. It does not assert that finite
prime-pair support would violate this bound.

## Verification

The file compiles. Axiom audits for the centered rows, the actual support bound,
and the finite weighted support bound print only propext, Classical.choice,
and Quot.sound. No new sorry or axiom was introduced in the development file.
No incomplete proof was submitted.
