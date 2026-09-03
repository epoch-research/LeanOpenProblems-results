import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_64 : blockPrimeCoverageCheck 64=true := by decide +kernel
theorem block_prime_coverage_65 : blockPrimeCoverageCheck 65=true := by decide +kernel
theorem block_prime_coverage_66 : blockPrimeCoverageCheck 66=true := by decide +kernel
theorem block_prime_coverage_67 : blockPrimeCoverageCheck 67=true := by decide +kernel
theorem block_prime_coverage_68 : blockPrimeCoverageCheck 68=true := by decide +kernel
theorem block_prime_coverage_69 : blockPrimeCoverageCheck 69=true := by decide +kernel
theorem block_prime_coverage_70 : blockPrimeCoverageCheck 70=true := by decide +kernel
theorem block_prime_coverage_71 : blockPrimeCoverageCheck 71=true := by decide +kernel
theorem block_prime_coverage_72 : blockPrimeCoverageCheck 72=true := by decide +kernel
theorem block_prime_coverage_73 : blockPrimeCoverageCheck 73=true := by decide +kernel
theorem block_prime_coverage_74 : blockPrimeCoverageCheck 74=true := by decide +kernel
theorem block_prime_coverage_75 : blockPrimeCoverageCheck 75=true := by decide +kernel
theorem block_prime_coverage_76 : blockPrimeCoverageCheck 76=true := by decide +kernel
theorem block_prime_coverage_77 : blockPrimeCoverageCheck 77=true := by decide +kernel
theorem block_prime_coverage_78 : blockPrimeCoverageCheck 78=true := by decide +kernel
theorem block_prime_coverage_79 : blockPrimeCoverageCheck 79=true := by decide +kernel

theorem block_prime_coverages_4 (i : ℕ) (hi0 : 64 ≤ i) (hi1 : i < 80) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_64
  · exact block_prime_coverage_65
  · exact block_prime_coverage_66
  · exact block_prime_coverage_67
  · exact block_prime_coverage_68
  · exact block_prime_coverage_69
  · exact block_prime_coverage_70
  · exact block_prime_coverage_71
  · exact block_prime_coverage_72
  · exact block_prime_coverage_73
  · exact block_prime_coverage_74
  · exact block_prime_coverage_75
  · exact block_prime_coverage_76
  · exact block_prime_coverage_77
  · exact block_prime_coverage_78
  · exact block_prime_coverage_79

#print axioms block_prime_coverages_4
end Erdos7No9Certificate
