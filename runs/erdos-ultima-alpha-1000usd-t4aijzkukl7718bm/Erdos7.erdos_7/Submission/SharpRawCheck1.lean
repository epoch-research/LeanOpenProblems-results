import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_5 : (primeRange 5000 1000).foldl roundedStep (349324668,816072447) = (377655260,818229175) ∧
    ((primeRange 5000 1000).map Nat.log2).sum = 1368 := by
  decide +kernel

lemma chunk_info_6 : (primeRange 6000 1000).foldl roundedStep (377655260,818229175) = (404074231,819927831) ∧
    ((primeRange 6000 1000).map Nat.log2).sum = 1404 := by
  decide +kernel

lemma chunk_info_7 : (primeRange 7000 1000).foldl roundedStep (404074231,819927831) = (426295223,821164254) ∧
    ((primeRange 7000 1000).map Nat.log2).sum = 1284 := by
  decide +kernel

lemma chunk_info_8 : (primeRange 8000 1000).foldl roundedStep (426295223,821164254) = (447512157,822206007) ∧
    ((primeRange 8000 1000).map Nat.log2).sum = 1409 := by
  decide +kernel

lemma chunk_info_9 : (primeRange 9000 1000).foldl roundedStep (447512157,822206007) = (467786023,823097714) ∧
    ((primeRange 9000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

end Erdos7SharpRawPrefix
