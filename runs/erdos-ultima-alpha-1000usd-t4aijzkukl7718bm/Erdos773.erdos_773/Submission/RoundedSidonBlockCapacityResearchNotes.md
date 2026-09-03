# Full interval packing and the rounded full-block ceiling

The original conjecture is NOT settled. `Spec.lean` was not changed. Its
sole admission remains at line 17287, for 0 < epsilon < 1/3. The established
unconditional endpoint is eventual M(N) >= N^(2/3). No incomplete proof was
submitted.

## New verified modules

* `FullIntervalSquareCapacity.lean`
* `RoundedSidonBlockCapacity.lean`

Both compile without warnings or admissions and have built oleans. All eight
printed audits use only propext, Classical.choice, and Quot.sound.

Logs:

* /tmp/full-interval-square-capacity.log
* /tmp/rounded-sidon-block-capacity.log
* /tmp/spec-rounded-capacity-check.log

## Arbitrarily labeled disjoint full intervals

`FullIntervalSquareCapacity` allows an arbitrary decidable label type and
an arbitrary natural start for each label. Its roots are the union of
[start(i), start(i)+H]. There is no common-modulus or modular-pair-matching
hypothesis.

For 0<T and 10*T<=H, associate to (i,u), T<=u<=2*T, the key

    floor(u*(start(i)+5*T)/T^2).

`key_collision` is a valid q=1 specialization of the existing close-center
collision theorem. Equal keys force equal positive square differences with
both endpoints in their corresponding FULL intervals. If the whole square
union is Sidon, endpoint uniqueness and disjointness of the intervals then
identify both the label and gap. This is `key_injective`.

Counting keys below the root height N gives `gap_capacity`:

    |I|*(T+1)*T <= 2*N+T.

Taking T=floor(H/10) proves `squared_width_capacity`, for H>=10:

    |I|*H^2 <= 1200*N.

The empty label set is included. This is a fullness-dependent capacity
bound, NOT a bound for arbitrary sparse selections from these intervals.

## Application to the exact rounded construction

Use the definitions from `RoundedSidonBlocks`, with marks A subset [0,L],
L>0, blocks of width H, and declared root height

    N = 65*L*(H+1).

If the FULL square-value union is Sidon, the generic interval capacity gives,
for H>=10:

    |A|*H^2 <= 78000*L*(H+1),
    |A|*(H+1) <= 312000*L.

These are `squared_width_capacity` and `mass_bound` in the new rounded
namespace. No Sidon condition on the ordinary marks is needed for these two
statements; the previously verified block separation suffices.

If A itself is an ordinary Sidon set, the elementary modular bound at
modulus one gives |A|^2<=5*L. Combining this with the mass bound, and handling
H<10 separately, proves `full_union_cube_bound` FOR EVERY H:

    |union of full value blocks|^3 <= 1560000*(L*(H+1))^2.

`full_union_real_bound` rewrites it at the declared height as

    |union of full value blocks| <= 8*N^(2/3).

Thus the proposed three-quarter count cannot be obtained just by proving
compatibility of the whole rounded blocks at the nominal parameters. The
partial-union theorem from `RoundedSidonBlocks` is still valid: this new
ceiling does not apply to arbitrary selected subsets of its blocks.

## Main gap

No compatible near-linear partial selector, useful new collision-count
saving, or unrestricted fixed-power upper bound was obtained. The exact
allowed-alphabet permutation carrier was reviewed, but no proof of its
eventual Sidonness and no counterexample to that eventual hypothesis was
found. Its single-transposition rigidity still does not cover arbitrary
permutation collisions.

`Spec.lean` SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
