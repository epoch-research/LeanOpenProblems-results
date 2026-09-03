import Submission.ContinuousIntervalInterpolation

/-! A small exact check that a lattice chord patch can strictly strengthen
an envelope. This is not a bound for all numbers of primes. -/
namespace Erdos970.ContinuousInterval

private noncomputable def q3 (i : ℕ) : ℝ := if i = 0 then 1 / 2 else if i = 1 then 1 / 3 else 1 / 5
private def cells3 (i : ℕ) : List ℕ := if i = 2 then [9] else []

/-- Before patching the cell [9,10], the lower envelope vanishes at 9.5. -/
theorem unpatched_three_at_nine_and_half : (envelope q3 3 (19 / 2)).1 = 0 := by
  norm_num [envelope, q3, stepLower, stepUpper, clip]

/-- The chord from the exact endpoint values at 9 and 10 is positive at 9.5. -/
theorem patched_three_at_nine_and_half :
    (patchedEnvelope q3 cells3 3).1 (19 / 2) = 1 / 20 := by
  norm_num [patchedEnvelope, chordPatches, q3, cells3, stepLower, stepUpper,
    clip, patchLower, patchUpper, chord]

#print axioms unpatched_three_at_nine_and_half
#print axioms patched_three_at_nine_and_half
end Erdos970.ContinuousInterval
