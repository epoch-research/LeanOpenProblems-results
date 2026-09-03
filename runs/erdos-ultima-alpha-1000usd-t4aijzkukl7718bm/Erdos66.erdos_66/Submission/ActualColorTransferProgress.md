# Disjoint curve palettes and actual coarse-color assemblies

## Original task status

The original existential conjecture is still unresolved. Spec.lean is
unchanged, retaining its original statement, import, and sorry. No proof
or disproof has been submitted.

Five new production files compile with current oleans:

1. DisjointPaletteAssemblyExplore.lean
2. OrientedEdgeRepairExplore.lean
3. PaletteL1RepairExplore.lean
4. DisjointCurvePaletteExplore.lean
5. ActualColorRootTransferExplore.lean

ActualColorTransferAudit.lean checks 15 principal declarations. All use only
propext, Classical.choice, and Quot.sound. There are no new placeholders or
axioms in the production files.

## 1. An actual-set identity with overlapping coarse colors

For pairwise disjoint fine palettes P_i in a finite abelian group G and
arbitrary coarse finite sets B_i in an abelian group H, define

  A = union_i (P_i x B_i).

`assembly_pairCount` proves exactly

  r_A(z,q) = sum_ij r_(P_i,P_j)(z) r_(B_i,B_j)(q).

No disjointness of B_i is required. `assembly_error` transfers an L1 error
E between the fine mixed-count matrices P and C to actual-set error at
most M E when every coarse mixed count at q is at most M.

## 2. A disjoint palette with only O(h) matrix error

Start with h distinct nonzero, pairwise nonopposite parameters u_i in an
odd finite field F. Assume

  h^2 < |F|,      2h+1 < |F|.

For C_i={(x,x^2/u_i)}, `exists_disjoint_curve_palette` selects pairwise
disjoint palettes P_i such that for EVERY fine target z,

  sum_ij |r_(P_i,P_j)(z)-r_(C_i,C_j)(z)| <= 10h+8.

The palettes are selected before any later coarse data.

Construction:
- Erase the common origin from each C_i, obtaining disjoint E_i.
- Choose one auxiliary parameter w outside +/- all u_i.
- Embed each unordered label pair i<j at a distinct nonzero point f_ij on
  the auxiliary parabola. Put +f_ij in D_i and -f_ij in D_j.
- Set P_i=E_i union D_i.

The resulting P_i are disjoint. At fine origin their mixed count is 1
for i!=j and 0 for i=j. The reference curve counts are all 1, so the
matrix L1 error there is exactly h.

Away from origin, erased endpoints cost at most 2h in total. The entire
repair support lies on two auxiliary parabolas, so total base/repair cost
is at most 8h and repair/repair cost is at most 8. The common-lower-matrix
inequality then bounds L1 error by 10h+8. This argument retains every new/new
pair and does not sum an O(h) bound separately for each pair of colors.

## 3. Composition with the fixed-translate color selection

For p prime and p>h^2+4h+2, `exists_actual_pattern_for_later_colors` selects
one admissible a and one disjoint palette P_i BEFORE all later coarse data.

Let the later coarse color sets be B_x, x in a finite nonempty color type.
For a finite coarse-target set S define

  K_q(x,y) = r_(B_x,B_y)(q),
  mu_q = mean(K_q),
  var_q = mean_(x,y) (K_q(x,y)-mu_q)^2,
  diag_q = mean_x (K_q(x,x)-mu_q)^2.

Suppose 0<=K_q(x,y)<=M_q and weights w_q>=0 on S. Put

  Budget = sum_(q in S) w_q [16h^2 var_q+4h diag_q].

There is one assignment omega_i of the coarse colors to the fixed labels
such that the ACTUAL finite set

  A = union_i P_i x B_(omega_i)

satisfies, for every q in S and every fine target (t,s),

  w_q [r_A((t,s),q)-h^2 mu_q]^2
   <= 2 w_q [M_q(10h+8)]^2
      +12h [8 w_q mu_q^2 h^2 + Budget].

This is now an actual-set statement, rather than a parameter-multiplicity
root count. The coarse sets may overlap arbitrarily. It still uses a
finite family budget and a finite field-plane times coarse-group ambient.

## Remaining global issue

These theorems close the arbitrary coarse-overlap/origin-multiplicity gap
for this finite pipeline. They do not supply an infinite coarse profile
with the required budget, an integer carry transfer for changing periods,
or all-tail feasibility above thresholds independent of the final cutoff.

In particular the fine support of the disjoint palette is sparse. Keeping
it permanently as a low-residue restriction cannot produce a witness,
by the previously checked necessary residue equidistribution. A valid
infinite construction must eventually redistribute mass in the old fine
residues, not merely choose new coarse colors over a fixed sparse support.

A conceptual alternative considered but NOT formalized is the complete
partition by parallel parabolas y=x^2+i, i in F. Its full unweighted root
mean is exactly uniform, so it would not retain a sparse support restriction.
No compatible recursive coarse family or integer-prefix construction was
obtained from this observation. Do not treat it as a new theorem or a
solution of Erdős 66.
