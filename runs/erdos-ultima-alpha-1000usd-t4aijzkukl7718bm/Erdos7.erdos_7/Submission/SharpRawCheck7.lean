import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_35 : (primeRange 35000 1000).foldl roundedStep (752741182,829619286) = (760092838,829705633) ∧
    ((primeRange 35000 1000).map Nat.log2).sum = 1380 := by
  decide +kernel

lemma chunk_info_36 : (primeRange 36000 1000).foldl roundedStep (760092838,829705633) = (767859774,829794306) ∧
    ((primeRange 36000 1000).map Nat.log2).sum = 1485 := by
  decide +kernel

lemma chunk_info_37 : (primeRange 37000 1000).foldl roundedStep (767859774,829794306) = (775111938,829874940) ∧
    ((primeRange 37000 1000).map Nat.log2).sum = 1410 := by
  decide +kernel

lemma chunk_info_38 : (primeRange 38000 1000).foldl roundedStep (775111938,829874940) = (781932368,829948754) ∧
    ((primeRange 38000 1000).map Nat.log2).sum = 1350 := by
  decide +kernel

lemma chunk_info_39 : (primeRange 39000 1000).foldl roundedStep (781932368,829948754) = (789092232,830024338) ∧
    ((primeRange 39000 1000).map Nat.log2).sum = 1440 := by
  decide +kernel

end Erdos7SharpRawPrefix
