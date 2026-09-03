# Degree-six norm-torus pencils: a checked obstruction, not a target proof

Let F=F_q, K=F_(q^6), E=F_(q^3), and let xi have degree6 over F. Write xi'=xi^(q^3) and y_t=(xi+t)/(xi'+t), t in F. These values lie in the norm-one group of order q^3+1. No fixed-excess strong-B3 subset or efficient quotient selector has been established.

For monic cubics P,Q with roots in F (multiplicities allowed), equality of the corresponding triple products is equivalent to

    P(xi)Q(xi')-Q(xi)P(xi')=0.

Degree<6 ensures the evaluations of nonzero P,Q at xi,xi' do not vanish. Independent P,Q span a pencil W in the four-dimensional space V=F[X]_(<=3). After extending scalars to an algebraic closure, put

    U_j={P in V:P(xi^(q^j))=P(xi^(q^(j+3)))=0},  j=0,1,2.

Each U_j has dimension2. The three determinant equations say precisely that W meets all three U_j nontrivially: each is the condition that the two-dimensional evaluation map restricted to W has rank at most1.

The six conjugates are distinct. Thus U_i intersect U_j={0} when i!=j: a polynomial of degree at most3 cannot vanish at four distinct points. Consequently these are three pairwise skew projective lines in P(V).

## The degeneracy possibility is ruled out

Any three pairwise skew lines in P^3 can be put in the form

    U_0=span(e0,e1), U_1=span(e2,e3),
    U_2=span(e0+e2,e1+e3).

Indeed, the first two give a direct-sum decomposition, and the third is the graph of an invertible map between their two-dimensional summands.

In Plucker coordinates p_ij for W, meeting these three lines imposes

    p23=0, p01=0, p01-p03+p12+p23=0.

Hence p12=p03, and the Grassmannian equation

    p01*p23-p02*p13+p03*p12=0

restricts to

    p02*p13=p03^2.

This is a smooth conic in every characteristic, including2: a singular point would have p02=p13=0, and the equation would then force p03=0. There is no such projective point. The canonical determinant identities were independently checked by exact Sympy expansion.

Frobenius permutes the three U_j, so the conic of pencils is defined over F. A smooth conic over a finite field has q+1 rational points. Thus the idea of choosing a genuine degree-six xi so that this pencil conic degenerates into an anisotropic rank-two form is not available.

## What this does not prove

A rational pencil need not contain two different fully split monic cubics. Establishing their existence and distribution is a separate arithmetic problem. Likewise, even many modular collisions would not by themselves exclude a sufficiently large selected subset or every possible integer lift. No pruning threshold, quotient construction, or interval asymptotic is proved here.

This calculation closes only the specific degenerate-conic possibility. It neither proves nor disproves the theorem in Spec.lean. That file remains unchanged with both admitted targets.
