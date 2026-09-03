import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_70 : (primeRange 70000 1000).foldl roundedStep (955899720,831348891) = (960895734,831378465) ∧
    ((primeRange 70000 1000).map Nat.log2).sum = 1568 := by
  decide +kernel

lemma chunk_info_71 : (primeRange 71000 1000).foldl roundedStep (960895734,831378465) = (965694246,831406470) ∧
    ((primeRange 71000 1000).map Nat.log2).sum = 1520 := by
  decide +kernel

lemma chunk_info_72 : (primeRange 72000 1000).foldl roundedStep (965694246,831406470) = (970199492,831432398) ∧
    ((primeRange 72000 1000).map Nat.log2).sum = 1440 := by
  decide +kernel

lemma chunk_info_73 : (primeRange 73000 1000).foldl roundedStep (970199492,831432398) = (974316380,831455776) ∧
    ((primeRange 73000 1000).map Nat.log2).sum = 1328 := by
  decide +kernel

lemma chunk_info_74 : (primeRange 74000 1000).foldl roundedStep (974316380,831455776) = (978839435,831481121) ∧
    ((primeRange 74000 1000).map Nat.log2).sum = 1472 := by
  decide +kernel

end Erdos7SharpRawPrefix
