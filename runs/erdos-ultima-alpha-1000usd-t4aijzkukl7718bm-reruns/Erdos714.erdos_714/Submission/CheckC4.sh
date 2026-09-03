#!/bin/sh
set -eu
cp Submission/C4.lean /tmp/C4Axioms.lean
printf '\n#print axioms Erdos714Finite.second_instance\n' >> /tmp/C4Axioms.lean
lake env lean /tmp/C4Axioms.lean
