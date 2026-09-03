import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_45 : (primeRange 45000 1000).foldl roundedStep (822683628,830354472) = (828534672,830408090) ∧
    ((primeRange 45000 1000).map Nat.log2).sum = 1290 := by
  decide +kernel

lemma chunk_info_46 : (primeRange 46000 1000).foldl roundedStep (828534672,830408090) = (834570861,830462231) ∧
    ((primeRange 46000 1000).map Nat.log2).sum = 1350 := by
  decide +kernel

lemma chunk_info_47 : (primeRange 47000 1000).foldl roundedStep (834570861,830462231) = (840851924,830517364) ∧
    ((primeRange 47000 1000).map Nat.log2).sum = 1425 := by
  decide +kernel

lemma chunk_info_48 : (primeRange 48000 1000).foldl roundedStep (840851924,830517364) = (846656888,830567268) ∧
    ((primeRange 48000 1000).map Nat.log2).sum = 1335 := by
  decide +kernel

lemma chunk_info_49 : (primeRange 49000 1000).foldl roundedStep (846656888,830567268) = (852967523,830620449) ∧
    ((primeRange 49000 1000).map Nat.log2).sum = 1470 := by
  decide +kernel

end Erdos7SharpRawPrefix
