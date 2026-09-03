# Exact-inversion full-alphabet carry obstruction

This is not a settlement of Erdős 773. The original conjecture and its sole
admission are unchanged.

## Verified result

`ExactInversionCarryObstacle.lean` imports only FormalConjecturesUtil and
compiles without warnings or admissions. All printed audits use only
propext, Classical.choice and Quot.sound. Build log:

    /tmp/exact-inversion-carry-final.log

The four roots are

    45611852, 72029084, 57841556, 62633732.

Their base-nine words, most significant digit first, are

    [1,0,4,7,3,8,6,2,5]
    [1,6,0,4,7,3,2,8,5]
    [1,3,0,7,4,8,6,2,5]
    [1,4,0,7,6,3,2,8,5].

Each is a permutation of the entire alphabet 0,...,8, has fixed positive
end digits 1 and 5, and has exact inversion count 13. Their squares satisfy

    45611852^2 + 72029084^2 = 57841556^2 + 62633732^2
                           = 7268629984748960.

The Lean file proves the evaluations, permutations, ends, inversion counts,
collision and non-Sidonness of this exact-inversion class. It also proves by
ring normalization the symbolic norm difference

    -B^5*(B-9)*(B-1)*(2*B^8+B^7-2*B^6+5*B^5+6*B^2+4*B+2).

## Exploratory screen

Research/ExactInversionScreen.cpp enumerated every base-nine full permutation
with nonzero leading digit and grouped them by both end digits and exact
inversion count. It checked 67,635,200 unordered square pairs, including
repeated summands, with exact unsigned integer arithmetic. Three repeated
sums were found:

    ends (1,0), inversion 20:
      64290204^2 + 82811124^2 = 69493644^2 + 78495516^2
    ends (1,5), inversion 13:
      45611852^2 + 72029084^2 = 57841556^2 + 62633732^2
    ends (2,0), inversion 22:
      105079932^2 + 122067108^2 = 109913652^2 + 117733428^2.

Only the second is packaged in the new Lean file. The others are exploratory
outputs, not additional formal theorems. The leading-1, constant-3 classes
were collision-free in this finite screen. All 5040 uniform relabelings of
the second example that would send its ends to 1 and 3 failed to preserve
the identity. These checks should not be repeated or treated as asymptotics.

## Scope

The example refutes the blanket claim that fixed positive ends and an exact
inversion count make full-alphabet permutations square-Sidon. It does not
refute the special ends (1,3), a prime-base variant, every inversion class,
or the existence of a large Sidon subclass. In particular it does not prove
the negation of the original eventual lower bound. No actual asymptotic
lower exponent or upper exponent was improved in this continuation.
