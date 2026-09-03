# Arbitrary prefix limits of flat finite cyclic templates

## Original task status

Erdős 66 is still unresolved. Spec.lean is unchanged with its original
sorry; no proof has been submitted.

## Completed results

CyclicPrefixPatchExplore.lean compiles and has a built olean. Its principal
results are audited in CyclicPrefixPatchAxiomCheck.lean and depend only on
propext, Classical.choice, and Quot.sound.

1. count_error_of_agree_off: if finite subsets B,C of an abelian group
   agree outside S, their ordered self-counts differ by at most 2|S| at
   every target.

2. patch_error: replacing membership in the first L representatives of
   ZMod N by an arbitrarily prescribed set changes each cyclic count by
   at most 2L.

3. exists_flat_with_prescribed_prefix: for any divergent sublinear mean
   f(N), any natural prefix length L(N) with L(N)/f(N) -> 0, and ANY set A,
   the uniformly flat cyclic templates can be chosen to agree with A at
   all n < min(L(N),N).

4. slow_prefix: floor(sqrt(f(N))) tends to infinity and is o(f(N)).

5. every_set_is_a_cyclic_prefix_limit: consequently EVERY A is the
   eventual pointwise prefix limit of uniformly flat cyclic templates.

6. logarithmic_templates_with_arbitrary_prefix_limit: for any c>0 and
   any A, there are C_N subset ZMod N with

      for each n, eventually (n mod N in C_N iff n in A),

   while for every sequence of target residues z_N,

      cyclicCount(C_N,z_N)/log N -> c.

## Scope

This is a real finite prefix-replacement result, but it is not the
uniform whole-integer-prefix estimate in CompactnessExplore.lean. Even
A=empty satisfies its conclusion. In particular, neither cyclic flatness
alone nor adding eventual agreement at each fixed coordinate yields the
representation limit required by Spec.lean.

No control over the transition mixed counts at targets comparable to N
has been proved. A construction would need that additional information
(or a different approach), not merely pointwise convergence of the chosen
finite templates.

The stronger demand that the entire cyclic sets be exact modular prefixes
of A is not an available fix either: CyclicPrefixExplore.lean already proves
that a genuine witness's modular prefix has nonvanishing relative variation.
The needed full-prefix profile is inhomogeneous, not uniformly cyclic-flat.
The present patching result concerns only eventual agreement at each fixed
coordinate and does not contradict that earlier obstruction.
