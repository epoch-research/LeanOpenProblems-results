import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_15 : (primeRange 15000 1000).foldl roundedStep (548799383,825859450) = (563336693,826250610) ∧
    ((primeRange 15000 1000).map Nat.log2).sum = 1404 := by
  decide +kernel

lemma chunk_info_16 : (primeRange 16000 1000).foldl roundedStep (563336693,826250610) = (576027674,826571283) ∧
    ((primeRange 16000 1000).map Nat.log2).sum = 1334 := by
  decide +kernel

lemma chunk_info_17 : (primeRange 17000 1000).foldl roundedStep (576027674,826571283) = (589007277,826880397) ∧
    ((primeRange 17000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

lemma chunk_info_18 : (primeRange 18000 1000).foldl roundedStep (589007277,826880397) = (600366131,827136951) ∧
    ((primeRange 18000 1000).map Nat.log2).sum = 1316 := by
  decide +kernel

lemma chunk_info_19 : (primeRange 19000 1000).foldl roundedStep (600366131,827136951) = (612492348,827396111) ∧
    ((primeRange 19000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

end Erdos7SharpRawPrefix
