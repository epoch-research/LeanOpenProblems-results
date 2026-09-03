import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_95 : (primeRange 95000 1000).foldl roundedStep (1058456560,831875404) = (1062412715,831892710) ∧
    ((primeRange 95000 1000).map Nat.log2).sum = 1520 := by
  decide +kernel

lemma chunk_info_96 : (primeRange 96000 1000).foldl roundedStep (1062412715,831892710) = (1065885958,831907750) ∧
    ((primeRange 96000 1000).map Nat.log2).sum = 1344 := by
  decide +kernel

lemma chunk_info_97 : (primeRange 97000 1000).foldl roundedStep (1065885958,831907750) = (1069252623,831922181) ∧
    ((primeRange 97000 1000).map Nat.log2).sum = 1312 := by
  decide +kernel

lemma chunk_info_98 : (primeRange 98000 1000).foldl roundedStep (1069252623,831922181) = (1072798738,831937219) ∧
    ((primeRange 98000 1000).map Nat.log2).sum = 1392 := by
  decide +kernel

lemma chunk_info_99 : (primeRange 99000 1000).foldl roundedStep (1072798738,831937219) = (1076322120,831952011) ∧
    ((primeRange 99000 1000).map Nat.log2).sum = 1392 := by
  decide +kernel

end Erdos7SharpRawPrefix
