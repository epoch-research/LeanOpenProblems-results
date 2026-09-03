# Nearby-modulus investigation

`Spec.lean` is still unproved and undisproved. Its original `sorry` is unchanged.

`NearbyPrimeCarryExplore.lean` defines the integer lift

    curveLift(p,u,x) = p*x + (u*x^2 mod p).

For p<=q and a mixed representation

    curveLift(p,u,x) + curveLift(q,v,y) = n,

it proves the exact carry identity

    q*(x+y) + (u*x^2 mod p) + (v*y^2 mod q) = n+(q-p)*x.

When x<p and p>0, the high-digit sum obeys

    n/q - 1 <= x+y <= n/q + (q-p),

so at most q-p+2 carry classes occur. For p=q these are the usual two cases.

Reduction modulo p gives

    u*x^2 + v*y^2 + (q-p)*y
      = n + (q-p)*floor(v*y^2/q)       in ZMod p.

Thus unequal moduli introduce a quotient term depending on the curve variable.
After fixing x+y, the equation is not the quadratic equation used by the
same-field character-fiber construction. A small number of carry cases does
not justify dropping this term, or asserting the old root-count formula.

The file compiles; the main results pass the permitted-axiom audit in
`NearbyPrimeCarryAxiomCheck.lean`. No uniform mixed-count estimate at the
logarithmic scale, and no infinite gluing theorem, has been obtained.
