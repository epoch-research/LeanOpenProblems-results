# Direct maximality argument checked

The original conjecture is still neither proved nor disproved. `Spec.lean`
is unchanged and contains its original `sorry`.

`MaximalityBarrierExplore.lean` defines the asymptotic upper condition

    UpperTail(A,c) := for every epsilon>0, eventually r_A(n)/log n <= c+epsilon.

It proves:

1. Finite insertion preserves UpperTail(A,c), using the existing bound that
   insertion raises any representation count by at most two.
2. UpperTail(A,c) implies r_A(n)/n -> 0. In particular the full set of natural
   numbers cannot satisfy this condition for any finite real c.
3. Every admissible A therefore has a strictly larger admissible set, by
   inserting any missing natural number. There is no inclusion-maximal member
   of this class.
4. For c>=0, the increasing sequence S_k={0,...,k-1} consists of admissible
   sets, but its union is all of N and is inadmissible. Thus chain closure,
   required by the proposed direct Zorn argument, is genuinely false.

The file compiles. `MaximalityBarrierAxiomCheck.lean` verifies that the two
main theorems use only propext, Classical.choice, and Quot.sound.

This does not negate the existential conjecture. It blocks only a direct
maximality inference from the asymptotic upper-bound class. Imposing a fixed
pointwise envelope changes the class and may restore compactness, but then
the missing task is to prove repairs preserve every envelope constraint.
The current one-target repair theorem does not establish this.

## Subsequent fixed-cap result

The fixed-envelope variant has now been tested directly. See
MaximalLogCapProgress.md: for every c>0 there is an inclusion-maximal set
under the fixed cap floor(c log(n+2))+10 with arbitrarily late holes and
near-cap peaks, and hence no finite normalized limit. Maximality is in
the full fixed-cap class. This refutes sufficiency of fixed-cap maximality,
not existence of a witness to the original conjecture.
