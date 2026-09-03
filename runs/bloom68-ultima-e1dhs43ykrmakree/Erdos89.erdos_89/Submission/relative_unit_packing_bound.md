# An elementary uniform relative-regulator packing bound

## Status and exact scope

This argument has been independently audited together with the actual-support
proof; see mixed_norm_packing_audit.md. It concerns a restricted arithmetic
family, NOT arbitrary planar finite sets. Together with
mixed_norm_actual_saturation.md and the audited constant identities, it rules
out making the actual FIXED-FIELD LIMITING constants of the full maximal-order
equal-radius polydisks tend to zero by varying fields. It does NOT rule out
varying-field pre-asymptotic sequences, give uniform finite-height or arbitrary
subset bounds, or prove either theorem of Spec.lean. No Lean file is edited.

## 1. Setting and the proposed bound

Let F have signature (r,s), r>=1, s>=1, e=r+2s, and E=F(i). More generally
only a quadratic extension E/F complexifying all real places is needed. Let
c be the relative involution. The relative archimedean norm-one group is

 T_infty=(S1)^r × (C*)^s.

At a complex F-place its E-coordinates are (z,z^(-1)). Write z=exp(t+i phi),
and use beta=2t. Put U_T={u in O_E*:N_E/F(u)=1}, w=|mu(E)|, and let R_rel
be the covolume of beta(U_T) in R^s, as in the audited reports. All roots of
unity of E have exact relative norm1: their norm is in mu(F)={±1} and positive
at a real F-place. The logarithmic kernel of U_T is exactly mu(E), by
Kronecker. Dirichlet gives a full-rank relative log lattice.

With Haar measure dtheta at each real angular factor, and dbeta dphi at each
complex factor, the compact quotient has volume

 vol(T_infty/U_T)=(2pi)^(r+s) R_rel/w.                   (1)

This follows by taking a log-lattice fundamental parallelepiped and the full
angular torus modulo its finite torsion kernel. Possible angular twists of
free units do not change the product volume.

CLAIM:

 R_rel >= w * 2^(-r) * (4pi)^(-s).                       (2)

This bound is exponential but much stronger for the present purpose than
using a factorial-height bound or the very small general Friedman--Skoruppa
constant. It exploits the exact quadratic norm-one relation.

## 2. A unit-free quotient neighborhood

Put q=2^(-r/s), and a=sqrt(q)/2, so 0<a<=1/2. Let B⊂T_infty have:

 - unrestricted S1 coordinates at the r real F-places;
 - at each complex F-place, -a/2<t<a/2 and -a/2<phi<a/2.

Thus the t and phi intervals each have width a, while the beta interval has
width2a. B is measurable, and

 vol(B)=(2pi)^r (2a²)^s=(2pi)^r (q/2)^s.                (3)

I claim B projects injectively into T_infty/U_T. If x,y∈B project to the
same class, u=x/y is an exact relative unit. At each complex F-place write
its coordinate z=exp(t+i phi). Then |t|<a and |phi|<a. At a real F-place
u has modulus1, so |sigma(u)-1|²<=4.

For the pair above a complex F-place,

 |z-1|² |z^(-1)-1|²
   = 16 [sinh²(t/2)+sin²(phi/2)]².                      (4)

For |t|<=1, cosh(t)-1<=t². For example, the nonnegative Taylor series gives
cosh(t)-1<=t²(cosh1-1)<=t² on this interval. Hence

 sinh²(t/2)<=t²/2,  sin²(phi/2)<=phi²/4,
 sinh²(t/2)+sin²(phi/2) <= 3a²/4 = 3q/16.

Multiplying (4) and the real-place bounds over ALL conjugate pairs of E
therefore gives

 |N_E/Q(u-1)|
   <=4^r [16(3q/16)²]^s
    =4^r (9q²/16)^s
    =(9/16)^s <1,                                    (5)

because q^(2s)=2^(-2r). But u is integral, so if u!=1 the norm of u-1 is a
nonzero integer and has absolute value at least1. Thus u=1 and x=y. This
argument includes all torsion units; they have not been silently discarded.

Since an injective quotient neighborhood has Haar volume no larger than the
compact quotient, combine (1) and (3):

 (2pi)^(r+s) R_rel/w >= (2pi)^r (q/2)^s.

This is exactly (2), since q^s=2^(-r).

## 3. Consequence for the audited arithmetic constant

The independently audited identity, with h_T>=1 and J>=1, is

 U(E/F)² = [2 h_T R_rel/(pi w)] (8/pi)^e (2pi)^s
             [sqrt(D_F)/kappa_F] J,

where kappa_F=Res zeta_F and Louboutin gives kappa_F<=sqrt(D_F).
Substitute (2), using e=r+2s. All factors simplify to

 U(E/F)² >= (2/pi) (4/pi)^r (32/pi²)^s.                 (6)

Both bases exceed1. Since r,s>=1, in particular

 U(E/F)² >= 256/pi^4,
 U(E/F) >= 16/pi² >1.62.                              (7)

No relative class-number, ramification, degree, or field-uniform height
assumption was inserted. Increasing r or s increases the displayed lower
bound. For s=0 use the already audited CM bound separately; the present
construction explicitly assumes s>0.

The independently audited actual-saturation theorem in
mixed_norm_actual_saturation.md supplies equality of the actual limit with U, making (6)--(7) lower bounds for actual
fixed-field limiting constants. In combination with the CM result, all these
full polydisk limiting constants are >=2/pi^(3/2), uniformly over fields.
This excludes the associated field-diagonal counterexample scheme. It does
not imply a uniform bound for ALL finite radii or for arbitrary selections
inside the windows. In particular it does NOT settle Spec.lean.

## 4. Checks needed in the independent audit

- Haar/covolume factor (2pi)^(r+s) R_rel/w with the WEIGHTED beta=2t convention.
- Norm identity (4) and multiplication over all complex embedding pairs ofE.
- Injectivity of B in the quotient, including roots of unity and angularly
  twisted free-unit generators.
- The inference volume(B)<=covolume(U_T) for this locally compact group.
- Simplification (6) and the exact limited scope, especially that it becomes
  an actual lower bound only AFTER the separate saturation theorem.
