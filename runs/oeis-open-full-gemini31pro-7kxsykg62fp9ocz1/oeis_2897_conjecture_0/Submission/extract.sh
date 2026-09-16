sed -n '20,36p' Submission/SpecMerged.lean > Submission/TestHugeSum3.lean
sed -n '37,189p' Submission/SpecMerged.lean > Submission/TestHugeSum2.lean
sed -n '190,251p' Submission/SpecMerged.lean > Submission/TestHugeSum6.lean
sed -n '252,280p' Submission/SpecMerged.lean > Submission/TestHugeSum7.lean
sed -n '281,338p' Submission/SpecMerged.lean > Submission/TestCommRing.lean
sed -n '339,378p' Submission/SpecMerged.lean > Submission/TestIfEquiv.lean
sed -n '379,461p' Submission/SpecMerged.lean > Submission/TestHugeSum14.lean
sed -n '462,601p' Submission/SpecMerged.lean > Submission/TestHugeSum9.lean
sed -n '602,619p' Submission/SpecMerged.lean > Submission/TestHugeSum12.lean
sed -n '908,962p' Submission/SpecMerged.lean > Submission/TestHugeSum8.lean

# Add back imports and namespace
for f in Submission/Test*.lean; do
    sed -i '1i\import FormalConjectures.Util.ProblemImports\nopen Finset Nat Polynomial MvPolynomial Finsupp\n' "$f"
done
