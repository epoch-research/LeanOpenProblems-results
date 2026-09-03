import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_80 : (primeRange 80000 1000).foldl roundedStep (1000101383,831595712) = (1004208912,831617012) ∧
    ((primeRange 80000 1000).map Nat.log2).sum = 1408 := by
  decide +kernel

lemma chunk_info_81 : (primeRange 81000 1000).foldl roundedStep (1004208912,831617012) = (1008469964,831638848) ∧
    ((primeRange 81000 1000).map Nat.log2).sum = 1472 := by
  decide +kernel

lemma chunk_info_82 : (primeRange 82000 1000).foldl roundedStep (1008469964,831638848) = (1012559622,831659557) ∧
    ((primeRange 82000 1000).map Nat.log2).sum = 1424 := by
  decide +kernel

lemma chunk_info_83 : (primeRange 83000 1000).foldl roundedStep (1012559622,831659557) = (1016387483,831678705) ∧
    ((primeRange 83000 1000).map Nat.log2).sum = 1344 := by
  decide +kernel

lemma chunk_info_84 : (primeRange 84000 1000).foldl roundedStep (1016387483,831678705) = (1020320068,831698144) ∧
    ((primeRange 84000 1000).map Nat.log2).sum = 1392 := by
  decide +kernel

end Erdos7SharpRawPrefix
