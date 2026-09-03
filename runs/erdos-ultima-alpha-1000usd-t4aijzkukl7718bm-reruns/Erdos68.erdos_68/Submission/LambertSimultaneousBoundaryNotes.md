# Simultaneous boundary-clearing index test

This is an external exact finite calculation, NOT a Lean theorem and NOT a
settlement of Erdős 68. Spec.lean is unchanged with its original sorry.
No proof or disproof has been obtained or submitted.

## Construction

Use the experiment indexing

    Q_K(E)=product_(d=2)^K(d! E^d-1),
    B_h=Q_K(E)S_h^L,
    H=K, D=2K+1.

For m consecutive output shifts, let C be the minimal common denominator of
B_H through B_(H+D+m-2), and b_h=C*B_h. Consider

    Lambda_m={w in Z^D: sum_(j=0)^(D-1) w_j*b_(H+i+j)=0 mod C
                       for i=0,...,m-1}.

If M is the m-by-D matrix of these boundary numerators modulo C, form the
integer matrix [M | C*I_m]. Its column lattice contains C*Z^m. If its Smith
invariants are s_1,...,s_m, the index of Lambda_m is

    I_m=C^m/product_i s_i.

This measures the exact arithmetic cost of simultaneous clearing, not the
lengths of useful lattice vectors or any nonvanishing property.

## Completed finite test

K=4,8,12,16,20,24. For each K, m ranges over the distinct values in
{1,2,3,4,K/2,K,2K+1}. All 39 cases completed. The retained integers C, I_m,
and all Smith invariants are exact. The logarithms below are diagnostics:

    K  m    log2 C     log2 I_m    log(I_m)/(m log C)
     4  1     53.492      53.492       1
     4  9     93.632     609.800       .723635
     8  1    213.059     213.059       1
     8 17    310.234    4147.595       .786427
    12  1    465.879     465.879       1
    12 25    633.144   12907.374       .815447
    16  1    813.967     813.967       1
    16 33   1059.990   29347.236       .838980
    20  1   1269.930    1269.930       1
    20 41   1596.981   55993.281       .855170
    24  1   1829.481    1829.481       1
    24  2   1838.020    3667.502       .997677
    24 24   2026.844   45528.526       .935949
    24 49   2243.560   95518.174       .868865

The finite results do not reveal a substantial reduction from the independent
congruence cost C^m in these windows. They do NOT prove an asymptotic lower
bound or rule out differently chosen windows, operators, or constraints.

## Independent audit

Construction accumulates Lambert divisor coefficients to obtain S_n^L.
The audit instead sums the finite geometric rows

    S_n^L=sum_(d=2)^n ((d!)^floor(n/d)-1)
                         / ((d!-1)*(d!)^floor(n/d)).

It also constructs Q_K by Sage polynomial multiplication, instead of the
construction's coefficient-array recurrence. It checks the minimal common
denominator and its divisibility into the known factorial-quotient clearing
factor. Finally, Hermite normal form of the transposed augmented matrix gives
an independent column-lattice basis. Its determinant agrees exactly with the
product of the Smith invariants in every case, and the index formula agrees
with the recorded I_m. All 39 audits passed.

Artifacts:

* /tmp/lambert_simultaneous_index.py
* /tmp/lambert_simultaneous_index.log
* /tmp/lambert_simultaneous_index.json
* /tmp/lambert_simultaneous_index_audit.py
* /tmp/lambert_simultaneous_index_audit.log

Both computations have completed. No computation is pending. The newer
uniform analytic operator bound still lacks a compatible infinite
nonvanishing construction. The carry and prime-block reviews in this pass
also supplied no unconditional infinite-occurrence or rank theorem. No new
Lean declaration or complete informal solution was obtained in this pass.
