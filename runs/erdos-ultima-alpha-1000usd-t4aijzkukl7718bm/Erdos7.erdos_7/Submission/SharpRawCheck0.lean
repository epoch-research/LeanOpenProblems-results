import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_0 : (primeRange 0 1000).foldl roundedStep (1000000,0) = (160681849,779751374) ∧
    ((primeRange 0 1000).map Nat.log2).sum = 1287 := by
  decide +kernel

lemma chunk_info_1 : (primeRange 1000 1000).foldl roundedStep (160681849,779751374) = (228892975,800021834) ∧
    ((primeRange 1000 1000).map Nat.log2).sum = 1346 := by
  decide +kernel

lemma chunk_info_2 : (primeRange 2000 1000).foldl roundedStep (228892975,800021834) = (277755577,808353307) ∧
    ((primeRange 2000 1000).map Nat.log2).sum = 1391 := by
  decide +kernel

lemma chunk_info_3 : (primeRange 3000 1000).foldl roundedStep (277755577,808353307) = (316155790,812974409) ∧
    ((primeRange 3000 1000).map Nat.log2).sum = 1320 := by
  decide +kernel

lemma chunk_info_4 : (primeRange 4000 1000).foldl roundedStep (316155790,812974409) = (349324668,816072447) ∧
    ((primeRange 4000 1000).map Nat.log2).sum = 1414 := by
  decide +kernel

end Erdos7SharpRawPrefix
