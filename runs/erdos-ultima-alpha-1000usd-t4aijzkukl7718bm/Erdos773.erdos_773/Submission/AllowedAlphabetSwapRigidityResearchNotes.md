# Verified single-transposition rigidity

This is NOT a settlement of Erdős 773. Spec.lean is unchanged, with its
sole admission at line 17287, for 0 < epsilon < 1/3. The completed
unconditional endpoint is still M(N) >= N^(2/3) eventually.

## New module

Submission/AllowedAlphabetSwapRigidity.lean imports the clean
AllowedAlphabetCandidate module. It contains no admissions. The five printed
axiom audits use only propext, Classical.choice, and Quot.sound.

Build log: /tmp/allowed-alphabet-swap-rigidity.log
Olean: .lake/build/lib/lean/Submission/AllowedAlphabetSwapRigidity.olean

## Generic arithmetic theorem

`single_swap_rigidity` uses integers B,L,x,y,z,w,u,v and natural exponents
i,j,k,l. It assumes:

* B >= 2 and IsCoprime B 12;
* all four roots lie in [L,2L), with L > 0;
* all four roots are 6 modulo B;
* 0 < u,v < B and k,l > 0;
* x-z = 6u B^i (B^k-1), w-y = 6v B^j (B^l-1);
* x^2+y^2 = z^2+w^2.

It proves i=j, u=v, k=l, x=w, and z=y. Primality of B is not assumed.

The lowest-position argument uses the congruence

    u(B^k-1)(x+z) = -12u mod B.

Coprimality and 0<u<B make this core indivisible by B. Thus the powers
B^i and B^j must agree. Cancelling these powers and reducing again modulo
B gives u=v, since |u-v|<B. The root-sum bounds then identify k and l;
the equal sums and differences identify both endpoints.

`base_coprime_twelve` verifies the relevant coprimality at B=6h+7 using

    (6h+7)^2 - 12(3h^2+7h+4) = 1.

## Connection to actual permutations: also complete

`leading_range` proves the sharper bounds

    B^(h+1) <= root(h,sigma) < 2 B^(h+1).

`constant_residue` proves root(h,sigma) = 6 modulo B.

`transposition_difference` proves, for a<b in Fin h, the exact identity

    root(h,sigma) - root(h,sigma * swap(a,b))
      = 6 (sigma(b)-sigma(a)) B^(a+1) (B^(b-a)-1),

where the digit-label difference is in the integers. `root_sum` and
`ofDigits_ofFn` give the checked finite-sum expansion used in this proof.

Finally, `transposition_rigidity` applies the generic theorem to two actual
increasing digit swaps. If their positive square differences agree, then
both original permutations, both swapped permutations, and the two swapped
positions agree. This is not merely an explicit-shape statement: the
permutation-to-shape connection has been checked in Lean.

## Scope

The theorem controls differences represented by ONE transposition on each
side. General pairs of permutations can differ at many positions. No proof
reducing an arbitrary square-sum collision to two single transpositions was
obtained. Thus eventual Sidonness of AllowedAlphabetCandidate.squares is
still unproved, and the conditional near-linear theorem cannot be applied.
No new unconditional lower exponent or original-conjecture disproof was
obtained. No incomplete proof was submitted.
