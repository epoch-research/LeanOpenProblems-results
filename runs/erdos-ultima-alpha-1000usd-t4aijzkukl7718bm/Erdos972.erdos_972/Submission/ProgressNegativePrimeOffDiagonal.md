# Exact negative raw off-diagonal at an irrational slope

The original conjecture remains UNSOLVED. `Spec.lean` remains unchanged,
including its original `sorry`. This is not an original-conjecture disproof.

New verified file: `Submission/NegativePrimeOffDiagonal.lean`.
Namespace: `Erdos972NegativePrimeOffDiagonal`.

Set alpha = 6 + sqrt(2)/100. The file proves:

* `slope_irrational`: alpha is irrational.
* `slope_gt_one`: alpha > 1.
* `slope_floor`: floor(alpha*n) = 6*n for all n <= 35.
* `offDiagonal_eq_of_floor`: for any alpha with that finite floor profile,
  primeFactorOffDiagonal alpha 35 3 3 = -2*log(5)*log(7).
* `irrational_negative_offDiagonal`: the actual raw prime-factor
  off-diagonal is strictly negative at the indicated irrational slope.

The computation is structural, not a brute-force numerical test. A nonzero
term has m,k>3 and distinct primes p,q>3. Its floor relation gives
k*q=6*m*p. Since q does not divide 6 or p, it divides m. Thus p*q<=35,
forcing (p,q)=(5,7) or (7,5). The only contributing tuples (m,p,k,q) are
(7,5,30,7) and (5,7,42,5), each with weight -log(5)*log(7).
The cutoff coefficients used are a_3(5)=a_3(7)=-1 and
 a_3(30)=a_3(42)=1.

Both principal theorems compile and their printed axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Scope limitations:

* This only rules out global nonnegativity of the raw off-diagonal.
* It does not give the sign of the centered off-diagonal.
* It does not refute a lower gap on sufficiently large common good scales.
* It gives no irrational slope with finitely many prime pairs.
* The decisive sufficient signed bound remains unproved.

No incomplete proof was submitted in this continuation.
