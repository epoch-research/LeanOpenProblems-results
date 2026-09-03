# Near-scale linear-extension diagnostic

## Status

This is numerical exploratory work, not a Lean theorem, not a certified
infeasibility result, and not a solution or disproof of Erdős 66.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

## Model

For a finite cutoff N, use the fractional probabilities

    p(i) = min(1, sqrt(4 log(i+e)/(pi (i+1))))   (0 <= i < N)

and the full truncated target q_N = p * p. This is an approximate square-root
logarithmic density model, NOT the exact harmonic fractional profile already
formalized elsewhere. The finite target arrays were computed by floating-point
FFT. Thus no asymptotic or exact harmonic claim follows from the tests.

`Diagnostics/transition_search.cpp` searches by swapping selected and
unselected points, keeping any prescribed old prefix fixed. It penalizes
squared excess above an absolute tolerance E from q_N, including the old/new
and new/new lookahead range. The total cardinality is fixed at the rounded
fractional mass. This is only a local optimization heuristic.

`Diagnostics/transition_milp.py` fixes an old set below N and tests the first
new window [N,2N). Its constraints are exactly of the linear form from
`TransitionLinearExplore.lean`, but the numerical right-hand sides are derived
from the approximate target above. It also fixes the number of new points.
It uses SciPy/HiGHS and does not produce a Lean-checked certificate.

## Observations, not mathematical conclusions

Starting with the saved 67-point prefix below 256:

* HiGHS found a 37-point extension in [256,512) whose computed first-window
  error was at most 5.974, below the tested tolerance 6.
* At tolerance 4, HiGHS reported infeasibility, also for the continuous
  relaxation. No exact certificate was extracted.
* At tolerance 5, the integer test timed out after 90 seconds without a
  feasibility conclusion.
* Freezing the tolerance-6 extension, the next test at cutoff 512 and the
  same tolerance was reported infeasible. Again this is not a certified
  theorem and says nothing about other prefixes or tolerances.

The saved point sets are `Diagnostics/prefix256.txt` and
`Diagnostics/extension512.txt`. The scripts expect target files/arguments
as documented by their command-line reads; the FFT target preparation used
NumPy and the displayed formula.

## Outcome

No scalable structural invariant or proof of extension feasibility emerged.
In particular, first-window feasibility must not be promoted to a compatible
infinite construction: the next window introduces quadratic new/new counts.
The unresolved task remains a genuine global construction with pointwise
o(log n) error, or a universal obstruction contradicting that asymptotic.
