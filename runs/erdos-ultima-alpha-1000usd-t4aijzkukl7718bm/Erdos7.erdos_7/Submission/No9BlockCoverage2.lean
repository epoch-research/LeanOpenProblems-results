import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_32 : blockPrimeCoverageCheck 32=true := by decide +kernel
theorem block_prime_coverage_33 : blockPrimeCoverageCheck 33=true := by decide +kernel
theorem block_prime_coverage_34 : blockPrimeCoverageCheck 34=true := by decide +kernel
theorem block_prime_coverage_35 : blockPrimeCoverageCheck 35=true := by decide +kernel
theorem block_prime_coverage_36 : blockPrimeCoverageCheck 36=true := by decide +kernel
theorem block_prime_coverage_37 : blockPrimeCoverageCheck 37=true := by decide +kernel
theorem block_prime_coverage_38 : blockPrimeCoverageCheck 38=true := by decide +kernel
theorem block_prime_coverage_39 : blockPrimeCoverageCheck 39=true := by decide +kernel
theorem block_prime_coverage_40 : blockPrimeCoverageCheck 40=true := by decide +kernel
theorem block_prime_coverage_41 : blockPrimeCoverageCheck 41=true := by decide +kernel
theorem block_prime_coverage_42 : blockPrimeCoverageCheck 42=true := by decide +kernel
theorem block_prime_coverage_43 : blockPrimeCoverageCheck 43=true := by decide +kernel
theorem block_prime_coverage_44 : blockPrimeCoverageCheck 44=true := by decide +kernel
theorem block_prime_coverage_45 : blockPrimeCoverageCheck 45=true := by decide +kernel
theorem block_prime_coverage_46 : blockPrimeCoverageCheck 46=true := by decide +kernel
theorem block_prime_coverage_47 : blockPrimeCoverageCheck 47=true := by decide +kernel

theorem block_prime_coverages_2 (i : ℕ) (hi0 : 32 ≤ i) (hi1 : i < 48) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_32
  · exact block_prime_coverage_33
  · exact block_prime_coverage_34
  · exact block_prime_coverage_35
  · exact block_prime_coverage_36
  · exact block_prime_coverage_37
  · exact block_prime_coverage_38
  · exact block_prime_coverage_39
  · exact block_prime_coverage_40
  · exact block_prime_coverage_41
  · exact block_prime_coverage_42
  · exact block_prime_coverage_43
  · exact block_prime_coverage_44
  · exact block_prime_coverage_45
  · exact block_prime_coverage_46
  · exact block_prime_coverage_47

#print axioms block_prime_coverages_2
end Erdos7No9Certificate
