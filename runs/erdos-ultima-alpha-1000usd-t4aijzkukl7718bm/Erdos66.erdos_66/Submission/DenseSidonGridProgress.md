# Dense finite Sidon grids

The conjecture in Spec.lean is unchanged and unresolved. The following is
only a counterexample to a proposed auxiliary extraction inference.

DenseSidonGridExplore.lean compiles. Six principal declarations are audited
in DenseSidonGridAudit.log with only propext, Classical.choice, Quot.sound.

For every odd prime p, define the integer set

    X = { val(x) + 2p val(x^2) : x in ZMod p }.

The no-carry base 2p separates both coordinates of a two-term sum. In the
odd field, equality of sum and sum of squares implies equality of unordered
pairs. Consequently X is Sidon, |X|=p, and X is contained in [0,2p^2).

The grid S=X+(4p^2)X satisfies

    |S|=p^2,  S subset [0,8p^4),  r_S(n)<=4 for EVERY natural n.

Thus its cardinality is at least 1/sqrt(8) times the square root of the
ambient endpoint. All counts are ordinary natural sum counts, not cyclic
surrogates. The bound uses the previously verified no-carry grid theorem.

For every m, choose a prime p>max(2,m(m+1)^2). Restrict the rows to m+1
members and keep p columns. Every coloring into m colors contains a
monochromatic rectangle. Thus S has no such Sidon coloring.

Main theorem: exists_dense_cap_four_not_sidon_colored.

Hence a cap and square-root density at one cutoff cannot justify bounded
Sidon coloring. This does not impose the all-scale sqrt(N log N) counting
profile of a hypothetical witness, nor exclude every more sophisticated
extraction theorem using that profile. No solution of Erdős 66 follows.
