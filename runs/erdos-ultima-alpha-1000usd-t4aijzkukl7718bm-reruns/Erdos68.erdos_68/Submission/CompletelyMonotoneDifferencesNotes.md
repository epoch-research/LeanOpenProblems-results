# General factorial-power finite-difference forms

This is auxiliary work, not a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.

## Verified results

`CompletelyMonotoneDifferences.lean` proves all statements in this section.
Its principal axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. It has a built olean and no proof holes.

For a real sequence f, use the backward-sign difference

    delta f(n) = f(n) - f(n+1).

A sequence is completely monotone here if delta^N f(n)>=0 for all N,n.
The file verifies closure under products, shifts, and taking differences;
the strict version is also closed under products and positive powers.
The discrete product rule is

    delta(fg)(n) = delta f(n)*g(n) + f(n+1)*delta g(n).

No integral representation is used in the Lean proof. Instead, the kernels

    K_k(n) = k! n! / (n+k+1)!

satisfy delta K_k = K_(k+1), so every K_k is strictly completely monotone.
Positive scaling and powers therefore show that

    (n!/(n+k+1)!)^j

is strictly completely monotone in n, for every j>=1 and k>=0. Summing in k
preserves strict positivity; the file verifies the required summability
and interchange with each finite difference. Thus the tails

    T_j(n) = (n!)^j * sum_(m>=n+1) 1/(m!)^j

satisfy delta^N T_j(n)>0 for every N,n.

A finite Newton telescoping identity gives an order bound for **any**
completely monotone sequence:

    sum_(k=0)^N delta^k f(n+1) + delta^(N+1) f(n) = f(n),
    0 <= delta^N f(n+1) <= f(n)/(N+1).

The second inequality also uses that the differences decrease with order.
Consequently delta^N T_j(n+1) tends to zero as N tends to infinity.

## Explicit integer column forms

Let

    E_j = sum_(m>=2) 1/(m!)^j,
    a_j(n) = ((n+1)!)^j,
    b_j(n) = sum_(m=2)^(n+1) (((n+1)!)^j / (m!)^j).

Every summand in b_j(n) is an integer. Define integer coefficients

    A_(N,j) = delta^N a_j(0),
    B_(N,j) = delta^N b_j(0).

The formal definitions use recursive integer differences, not a binomial
sum. The sign convention differs from the earlier D_(N,j), C_(N,j) by
multiplication by (-1)^N. The verified identity and bounds are

    A_(N,j) E_j - B_(N,j) = delta^N T_j(1),
    0 < A_(N,j) E_j - B_(N,j) < 2/(N+1).

The upper bound is uniform in j. Each fixed j thus supplies a sequence of
strictly positive integer forms tending to zero as N increases. The main
theorems are `tail_strictCM`, `column_form_identity`, `column_form_pos`,
`column_form_uniform_bound`, and `tendsto_column_forms`.

This resolves the general **sign of the total column residual** for all
orders and all powers. It does not assert positivity of every shifted
polynomial coefficient in the external falling-residue calculations.

## Unresolved target gap

These forms involve the separate E_j, whereas the target is

    alpha = sum_(j>=1) E_j.

The leading integer A_(N,j) depends on j. Rationality of alpha does not make
the individual forms integral, and summing forms with these different
leading coefficients does not give A*alpha-B. A common-leading-coefficient
construction with small total error and an integral total boundary is
still missing. In particular, the uniform error bound does not supply the
missing arithmetic compatibility.

No proof or disproof of the original conjecture has been obtained, and
no complete proof has been submitted.
