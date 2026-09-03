# Field-varying norm constants: research report and audit boundary

STATUS: Neither theorem of Spec.lean is proved. The calculation has now had
an independent audit, saved in field_norm_constant_audit.md. No fatal error
was found; the audit supplies the radial-normalized unitary Hecke character
argument, tail estimates, and split-prime switching details needed to turn the
analytic sketch into a fixed-field proof. The parent also checked the algebra,
source identities, volume factors, and geometric endpoint construction. This
is still a restricted mathematical result, not a Lean formalization or a
solution of the original uniform planar conjecture.

The diagonal counterexample logic is legitimate: if for fields F one has actual
families with limsup D(P) sqrt(log|P|)/|P| <= c_F and inf_F c_F=0, the sharp
uniform conjecture is false. One may fix the field before taking size to
infinity; a field-dependent starting threshold is not an objection.

## Notation and the reported CM calculation

Let E/F be a CM quadratic extension, e=[F:Q], DF=|disc F|, DE=|disc E|,
d=N(d_E/F), so DE=DF²d. Let S be the finite ramified primes, t=|S|,
q_p=Np, a_p=v_p(d_E/F), kappa_K=Res_(s=1) zeta_K(s), and w=|mu(E)|.
Let chi be the quadratic Hecke character; L(1,chi)=kappa_E/kappa_F. Set

 I = product_(p inert) (1-q_p^(-2))^(-1),
 R = product_(p ramified) (1-q_p^(-1))^(-1).

Project the actual maximal-order Minkowski polydisk
 P_R={z in O_E : |sigma_j(z)|<=R for every complex place j}
into one complex embedding. This is injective, and

 n_R ~ (2pi)^e R^(2e)/sqrt(DE).

Let A(X) count DISTINCT nonzero integral ELEMENT norms delta=N_E/F(z),
z in O_E, satisfying 0<tau_j(delta)<=X at all real places of F. The agent
reports the following fixed-field relative Landau--Bernays formula:

 A(X) ~ [2^(1-t)/sqrt(pi DF)] [sqrt(kappa_E)/kappa_F] sqrt(I R)
          X^e/sqrt(log(X^e)).                                      (1)

The logarithm is log(X^e). The proposed actual distance limit is consequently

 c(E/F)=lim_(R->infinity) D(P_R)sqrt(log n_R)/n_R
   = [2^(1-t)/sqrt(pi)] (2/pi)^e sqrt(DE/DF)
           [sqrt(kappa_E)/kappa_F] sqrt(I R).                       (2)

The actual endpoint sandwich is rigorous once (1) is available: for a fixed
C_E equal to TWICE a Minkowski covering radius, every z with all
|sigma z|<=2R-C_E is an actual
difference of two points of P_R, by rounding z/2 in the full O_E lattice.
Thus A((2R-C_E)²)<=D(P_R)<=A(4R²). For CM every norm representation has
|sigma_j z|²=tau_j(delta), so the representation bounds are automatic.

### Reported derivation of the element asymptotic (the analytic audit target)

The norm-IDEAL indicator b(a) has even inert valuations. Its Euler product is
 Z(s)=prod_(split or ramified)(1-q^(-s))^(-1)
       prod_(inert)(1-q^(-2s))^(-1),
 Z(s)²=zeta_F(s)L(s,chi) I(s)R(s).
Hence the ideal summatory leading constant is
 B_id=sqrt(kappa_F L(1,chi)/pi)*sqrt(I R).
This is not yet an element count.

For a positive delta, integral local norm conditions are: even valuation at
inert primes, no condition at split primes, and chi_p(delta)=1 at ramified
primes. At a ramified prime every nonnegative valuation is possible and
half the unit residues are allowed, including the dyadic conductor correctly.
The cyclic Hasse norm theorem gives a FRACTIONAL element of exact norm delta.

Use the finite conductor f=d_E/F, positive units U_F^+, and V={u in U_F^+:
u=1 modf}. If h_f^+ is the positive ray class number, phi_F(f)=|(O_F/f)^*|,
and R_V the ordinary log determinant of V, then
 h_f^+ R_V = h_F^+ R_F^+ phi_F(f)=kappa_F sqrt(DF) phi_F(f).
For any fixed ramified valuation vector the number of allowed unit residue
tuples is phi_F(f)/2^t. The prime-to-S twisted ideal series is
 Z_psi^S(s)=[L^S(s,psi)L^S(s,psi chi)]^(1/2)
            prod_(inert)(1-psi(p)²q^(-2s))^(-1/2).
Only twists psi=1,chi contribute a leading pole. Both are positive and equal
on the allowed tuples, giving factor2. Nontrivial log-unit modes have no
leading pole. Finite Fourier approximation and fixed-character Hecke theory
are asserted to justify equidistribution. The box average for generators of
an ideal of norm y<=X^e is
 (log(X^e/y))^(e-1)/((e-1)!R_V).
The radial integral of (log(1/u))^(e-1) on0<u<1 is (e-1)!, leaving precisely
2^(1-t)/(kappa_F sqrtDF) times B_id. Ramified valuations sum geometrically.
Even t=0 is included; the factor is2 because chi then already gives a
nontrivial narrow class character. It is not a literal fractional genus size.

To remove the integral class/unit obstruction, use the FINITE group
 H=ker(N:I_E->I_F)/{(u):u in E*, N(u)=1}.
The map a->a/bar(a) from fractional E-ideals onto H factors through Cl(E),
with kernel the strongly ambiguous classes. Given a local norm delta, choose
z0 in E* of exact norm delta and an integral ideal J with NJ=(delta). The
class of J/(z0) in H is the obstruction to an integral exact norm. Switching
a split-prime factor from bar(P) to P changes it by [P/bar(P)]. Split prime
reservoirs in finitely many ideal classes generate H and have divergent
reciprocal norm sums. Fixed-field local norm counting with finitely many
extra prime divisibility constraints allegedly shows almost all locally
admissible delta have enough reservoir factors to cancel every obstruction.
This proves leading saturation, not a quantitative uniform-in-field error.
The use of exact norm-one generators retains the unit obstruction.

### Algebraic lower bound if (1) is correct

Let Q_E=[O_E*:mu(E)O_F*] in{1,2}, and h_T=|H|>=1. The cited CM identities are
 R_E/R_F=2^(e-1)/Q_E,
 h_E/h_F=Q_E 2^(t-1) h_T.
The class number formula gives
 L(1,chi)=2^(t-1)(2pi)^e h_T/(w sqrt(DE/DF)).
Substitution into (2) yields

 c(E/F)²=[2h_T/(pi w)] (8/pi)^e [sqrt(DF)/kappa_F] J,
 J=I*product_(ramified p) q_p^(a_p/2)/(2(1-1/q_p)).               (3)

Every local factor of J is>=1 (a_p>=1 and sqrt(q)/(2(1-1/q))>=1 forq>=2).
Louboutin's unconditional estimate
 kappa_F <= [exp(1)log DF/(2(e-1))]^(e-1) <=sqrtDF
holds fore>=2, and the final inequality holds for F=Q as equality. The
second inequality uses1+logx<=x. Finally phi(w)<=2e and phi(m)>=sqrt(m/2)
give w<=8e². Therefore

 c(E/F)² >= (8/pi)^e/(4pi e²) >=4/pi³,
 c(E/F)>=2/pi^(3/2),

and the constants tend to infinity as e->infinity. Thus the reported
asymptotic would exclude this CM diagonal-counterexample family uniformly,
without any field-uniform starting threshold, GRH or Brauer--Siegel.
For Q(i)/Q, (1) is Landau--Ramanujan and c=4*kappa_LR/pi; (3) gives
c²=8I/pi², with kappa_LR²=I/2, an exact calibration.

## Mixed signature: reported upper capacity, not actual equality

Let F have signature(r,s), r>=1, e=r+2s, and E=F(i). Use the same full
E-polydisk. At each complex F-place the relative norm is a product of two
E-embedding coordinates, not their squared modulus. The norm-element box
has real bounds0<tau(delta)<=X and complex bounds|tau(delta)|<=X.
The reported version of (1) gains factor(2pi)^s, from archimedean volume
and covolume. It would give a legitimate UPPER distance constant

 limsup D(P_R)sqrt(log n_R)/n_R <= U(E/F),
 U(E/F)=[2^(1-t)/sqrtpi](2/pi)^e(2pi)^s sqrt(DE/DF)
           [sqrt(kappa_E)/kappa_F] sqrt(I R).                    (4)

No equality/saturation of balanced E-embedding sizes is asserted in this
mixed case. Product norm bounds alone do not give balanced representatives.

Define R_rel by a basis of exact relative units modulo roots of unity, using
one E-place over each complex F-place, and determinant of 2log|sigma(u)|.
Its rank is s; setR_rel=1 when s=0. For I_N=[O_F*:N O_E*], the cited identities
are |Am_st|=h_F 2^(t+r-1)/I_N, h_T=h_E/|Am_st|, and
 R_E/R_F=(I_N/2)R_rel.
Then the algebraic reformulation is

 U(E/F)²=[2 h_T R_rel/(pi w)] (8/pi)^e (2pi)^s
           [sqrtDF/kappa_F] J.                                (5)

Consequently U->0 in a degree-growing family would require
 R_rel=o(e² (pi/8)^e (2pi)^(-s)).
The available relative height-product theorem plus Voutier gives
 R_rel >= V(2e)^s/s!, V(d)=1/4*(loglog d/logd)^3.
This rules out U->0 for bounded s or s loge=o(e), but is insufficient when
s is proportional to e. No explicit family with U->0 was found.

Parent additionally checked Pazuki1406.0120, lines249--250: the general
Friedman--Skoruppa bound is R_L/R_K >=(c1*c2^[L:K])^[K:Q], with
c1=(11.5)^(-39),c2=1.15. These constants are FAR too weak to close (5) for
quadratic E/F; citing existence of an exponential bound is not sufficient.

## Cited analytic and arithmetic inputs

- Frei--Loughran--Newton1810.06024, lines311--413: number-field Frobenian
  Euler products and fixed-character Hecke factorization.
- Loughran--Matthiesen1904.12845, lines532--604: scalar Selberg--Delange.
- Browning--Newton1411.7775, lines18--35: cyclic Hasse norm theorem.
- Guo--Sheu--Yu1905.11649/classnoCMtoriNMJ.tex, lines95--102,792--797:
  h_T=(h_E/h_F)/(Q_E 2^(t-1)).
- Biswas1610.00733, lines265--315: strongly ambiguous class number formula.
- Garcia--Lee2007.10313/UEMTNF.tex, lines133--138: Louboutin residue bound.
- Akhtari--Vaaler1508.01969, lines350--409, and2008.06124, lines255--273,
  845--864,1429--1432: relative unit/regulator identities and height bounds.
- Brink--Moree--Osburn1003.1094, lines77--86,138--157: Bernays calibration.

The norm-element asymptotic is a derived claim, not an assertion that any
one cited paper already proves this exact box formula. Its audit boundary
must remain explicit. No original proof or disproof has been obtained.
