import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_80 : blockPrimeCoverageCheck 80=true := by decide +kernel
theorem block_prime_coverage_81 : blockPrimeCoverageCheck 81=true := by decide +kernel
theorem block_prime_coverage_82 : blockPrimeCoverageCheck 82=true := by decide +kernel
theorem block_prime_coverage_83 : blockPrimeCoverageCheck 83=true := by decide +kernel
theorem block_prime_coverage_84 : blockPrimeCoverageCheck 84=true := by decide +kernel
theorem block_prime_coverage_85 : blockPrimeCoverageCheck 85=true := by decide +kernel
theorem block_prime_coverage_86 : blockPrimeCoverageCheck 86=true := by decide +kernel
theorem block_prime_coverage_87 : blockPrimeCoverageCheck 87=true := by decide +kernel
theorem block_prime_coverage_88 : blockPrimeCoverageCheck 88=true := by decide +kernel
theorem block_prime_coverage_89 : blockPrimeCoverageCheck 89=true := by decide +kernel
theorem block_prime_coverage_90 : blockPrimeCoverageCheck 90=true := by decide +kernel
theorem block_prime_coverage_91 : blockPrimeCoverageCheck 91=true := by decide +kernel
theorem block_prime_coverage_92 : blockPrimeCoverageCheck 92=true := by decide +kernel
theorem block_prime_coverage_93 : blockPrimeCoverageCheck 93=true := by decide +kernel
theorem block_prime_coverage_94 : blockPrimeCoverageCheck 94=true := by decide +kernel
theorem block_prime_coverage_95 : blockPrimeCoverageCheck 95=true := by decide +kernel

theorem block_prime_coverages_5 (i : ℕ) (hi0 : 80 ≤ i) (hi1 : i < 96) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_80
  · exact block_prime_coverage_81
  · exact block_prime_coverage_82
  · exact block_prime_coverage_83
  · exact block_prime_coverage_84
  · exact block_prime_coverage_85
  · exact block_prime_coverage_86
  · exact block_prime_coverage_87
  · exact block_prime_coverage_88
  · exact block_prime_coverage_89
  · exact block_prime_coverage_90
  · exact block_prime_coverage_91
  · exact block_prime_coverage_92
  · exact block_prime_coverage_93
  · exact block_prime_coverage_94
  · exact block_prime_coverage_95

#print axioms block_prime_coverages_5
end Erdos7No9Certificate
