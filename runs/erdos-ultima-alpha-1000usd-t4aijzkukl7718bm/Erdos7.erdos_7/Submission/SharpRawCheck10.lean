import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_50 : (primeRange 50000 1000).foldl roundedStep (852967523,830620449) = (858625394,830667191) ∧
    ((primeRange 50000 1000).map Nat.log2).sum = 1335 := by
  decide +kernel

lemma chunk_info_51 : (primeRange 51000 1000).foldl roundedStep (858625394,830667191) = (864710282,830716461) ∧
    ((primeRange 51000 1000).map Nat.log2).sum = 1455 := by
  decide +kernel

lemma chunk_info_52 : (primeRange 52000 1000).foldl roundedStep (864710282,830716461) = (870223592,830760249) ∧
    ((primeRange 52000 1000).map Nat.log2).sum = 1335 := by
  decide +kernel

lemma chunk_info_53 : (primeRange 53000 1000).foldl roundedStep (870223592,830760249) = (875853384,830804137) ∧
    ((primeRange 53000 1000).map Nat.log2).sum = 1380 := by
  decide +kernel

lemma chunk_info_54 : (primeRange 54000 1000).foldl roundedStep (875853384,830804137) = (881294082,830845780) ∧
    ((primeRange 54000 1000).map Nat.log2).sum = 1350 := by
  decide +kernel

end Erdos7SharpRawPrefix
