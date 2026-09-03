# Interior rational local admissibility — not a settlement

Submission/Spec.lean remains unchanged and still contains its original sorry.
No proof of the conjecture, prime-pair lower bound, or irrational
counterexample has been obtained.

## New verified file

Submission/RationalInteriorAdmissibility.lean
Namespace: Erdos972RationalInteriorAdmissibility.

All four principal declarations compile and use only propext,
Classical.choice, and Quot.sound. The file contains no sorry declarations.

## Uniform prime nondivisor in a proportional interval

`theta_interval_le_log_of_all_dvd` proves that if every prime in (x,y]
divides a nonzero integer n, then

    theta(y)-theta(x) <= log n.

It compares the interval prime sum with the full divisor Mangoldt sum,
which equals log n.

`eventually_prime_not_dvd` proves, for every fixed A>0, a threshold B such
that, for every natural b>=B and every positive n<=A*b^2, there is a prime p
with

    b/4 < p <= b/3,    p does not divide n.

The threshold is uniform in n. The PNT gives interval logarithmic prime
mass at least b/24, whereas log n<=log A+2log b<b/24 for large b.

## Local admissibility inside the transfer window

`exists_interior_admissible_residue` proves that for every A>1 there is B
such that for all natural coprime a,b with

    b<a, a<=A*b, B<b,

there are natural r,c,t satisfying

    0<r<b, ar=bc+t, b/4<t<3b/4.

For every natural k,

    ak+c+1/4 < (a/b)*(bk+r) < ak+c+3/4.

Furthermore, at every prime ell there is k<=2 for which neither bk+r nor
ak+c is divisible by ell. Thus the two affine forms are locally admissible
in precisely the strict interior window required by RationalRoute.

Construction: choose a prime p in (b/4,b/3] not dividing ab. If a,b are both
odd, take t=2p; otherwise take t=p. This ensures gcd(t,a)=gcd(t,b)=1 and
removes the possible parity obstruction. Modular inversion of a modulo b
then supplies r and c. The existing rational local-residue lemmas check all
primes, including 2.

The fractions 1/4 and 3/4 in the window are real divisions, as confirmed
by inspecting the elaborated theorem type.

## Actual prime inputs, but not prime outputs

`exists_interior_prime_input_coprime_output` uses the preceding result and
the existing Dirichlet/CRT argument. With the same uniform slope threshold,
for every nonzero fixed modulus M and input bound P there exist p,q with

    P<p, p prime, gcd(q,M)=1,
    q+1/4 < (a/b)*p < q+3/4,
    floor((a/b)*p)=q.

There is NO upper bound on p here, and q is NOT asserted to be prime.
The modulus M is fixed before the prime input is selected.

## Unresolved arithmetic estimate

RationalRoute requires prime p AND prime q with

    b<=p, 8p<=b^2,

in this interior window. Neither condition missing from the new Dirichlet
conclusion can be assumed. Selecting a locally admissible residue class
also does not justify replacing the linked input intervals by an average
over unrestricted shifts. No uniform finite prime-pair estimate was proved.

An informal three-prime reformulation a*p-b*q=t (with t prime or twice prime)
was considered. The third variable has size b while the coefficients a,b
also have size b and the transfer restricts p to at most b^2/8. No applicable
uniform ternary-prime estimate in that range was established or imported.

No original conjecture statement or imports were changed. No incomplete
proof was submitted.

## Follow-up determinant-average review — no new theorem

The determinant-window sum was reexamined as a possible way to weaken the
uniform rational prime-pair estimate. No sufficient lower bound resulted.
The exact constraints are

    a*p-b*q=t, b/4<t<3b/4, b<=p, 8p<=b^2,

with both p and q prime. Varying t still links each determinant to a residue
class of p modulo b; it is not an unrestricted average of binary prime
counts over independent shifts and intervals. No existing row or rotation
estimate was substituted for this simultaneous-primality assertion.

Restricting t to primes, or twice primes for parity, also did not yield an
applicable uniform three-prime theorem in the required coefficient and
variable ranges. The reformulation alone supplies no new lower bound.

No additional Lean declaration or irrational counterexample was obtained
in this review. Spec.lean remains unchanged and unresolved. No incomplete
proof was submitted.
