import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_30 : (primeRange 30000 1000).foldl roundedStep (711536051,829089140) = (719897589,829203451) ∧
    ((primeRange 30000 1000).map Nat.log2).sum = 1330 := by
  decide +kernel

lemma chunk_info_31 : (primeRange 31000 1000).foldl roundedStep (719897589,829203451) = (727835540,829308634) ∧
    ((primeRange 31000 1000).map Nat.log2).sum = 1288 := by
  decide +kernel

lemma chunk_info_32 : (primeRange 32000 1000).foldl roundedStep (727835540,829308634) = (736794977,829423593) ∧
    ((primeRange 32000 1000).map Nat.log2).sum = 1510 := by
  decide +kernel

lemma chunk_info_33 : (primeRange 33000 1000).foldl roundedStep (736794977,829423593) = (745088999,829526806) ∧
    ((primeRange 33000 1000).map Nat.log2).sum = 1500 := by
  decide +kernel

lemma chunk_info_34 : (primeRange 34000 1000).foldl roundedStep (745088999,829526806) = (752741182,829619286) ∧
    ((primeRange 34000 1000).map Nat.log2).sum = 1410 := by
  decide +kernel

end Erdos7SharpRawPrefix
