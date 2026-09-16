#!/bin/bash
cat Submission/Helper.lean Submission/Helper2.lean Submission/Helper4.lean Submission/Helper5.lean Submission/Helper6.lean Submission/Helper7.lean Submission/Helper8.lean Submission/Helper9.lean Submission/Helper_mono.lean Submission/Helper10.lean Submission/Helper11.lean Submission/Helper12.lean Submission/Helper13.lean Submission/Helper14.lean Submission/Proof.lean > Submission/AllHelpers.lean
# Remove the import Mathlib and import Submission... from AllHelpers.lean
grep -v "^import " Submission/AllHelpers.lean > Submission/AllHelpers_clean.lean

# Now we need to insert AllHelpers_clean.lean into Spec.lean right before the sequence_of_fractions definition, or just before the theorem.
# Let's insert it before the theorem oeis_340738_conjecture_0
awk '/theorem oeis_340738_conjecture_0/ { system("cat Submission/AllHelpers_clean.lean") } { print }' Submission/Spec.lean.orig > Submission/Spec_merged.lean

