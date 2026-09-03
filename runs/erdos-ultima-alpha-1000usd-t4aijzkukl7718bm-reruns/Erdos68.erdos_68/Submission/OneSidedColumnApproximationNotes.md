# One-sided column approximation: an unresolved construction

This is informal research analysis, not a new Lean theorem and not a
settlement of Erdős 68. Spec.lean is unchanged with its original sorry.

Let

    alpha=sum_(n>=2) 1/(n!-1),
    S_K=sum_(n=2)^K 1/(n!-1),
    D_K=product_(n=2)^K (n!-1),
    E_(j,K)=sum_(n>K) 1/(n!)^j.

Then

    alpha=S_K+sum_(j=1)^J E_(j,K)+R_(J,K),
    R_(J,K)=sum_(n>K) 1/((n!)^J*(n!-1))>0.

For A a positive multiple of D_K and integers b_j, the exact form

    A*alpha - (A*S_K + sum_j b_j)
      = sum_j (A*E_(j,K)-b_j) + A*R_(J,K)

has integral coefficients. If every retained-column error lies in [0,eps],
this form is strictly positive and at most J*eps+A*R_(J,K). A family with
this upper bound tending to zero would prove irrationality.

The missing construction is quantitative ONE-SIDED simultaneous
approximation. Ordinary simultaneous Dirichlet approximation controls
absolute errors but not their common sign. A vector such as (theta,1-theta)
shows why the sign condition is not automatic. It cannot be asserted merely
because all the target column values are positive. The individual
irrationality theorems for E_j do not provide the required joint estimate.

For two-sided approximation, applying Dirichlet to the vector D_K*E_(j,K)
would give A=D_K*a with a bounded by a power of the accuracy parameter.
The errors are not additionally multiplied by D_K: approximation is being
applied to the already scaled vector. This avoids one unnecessary height
loss, but does not repair nonvanishing. Under rationality of alpha the
resulting total integer form could still be zero.

Qualitative density, even if the needed finite linear independence were
proved, would not bound the denominator A relative to the remainder
R_(J,K). Such a uniform quantitative bound remains essential. No such bound,
explicit one-sided family, or usable asymptotic Padé construction has been
obtained. The previous finite joint Padé calculations do not establish it.

This pass produced no new verified Lean declarations and no complete
informal proof awaiting formalization. No proof or disproof was submitted.
