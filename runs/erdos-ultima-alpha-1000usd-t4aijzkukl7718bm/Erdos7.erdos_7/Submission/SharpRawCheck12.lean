import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_60 : (primeRange 60000 1000).foldl roundedStep (908573340,831043947) = (913543102,831078219) ∧
    ((primeRange 60000 1000).map Nat.log2).sum = 1320 := by
  decide +kernel

lemma chunk_info_61 : (primeRange 61000 1000).foldl roundedStep (913543102,831078219) = (918401330,831111171) ∧
    ((primeRange 61000 1000).map Nat.log2).sum = 1305 := by
  decide +kernel

lemma chunk_info_62 : (primeRange 62000 1000).foldl roundedStep (918401330,831111171) = (923263233,831143630) ∧
    ((primeRange 62000 1000).map Nat.log2).sum = 1320 := by
  decide +kernel

lemma chunk_info_63 : (primeRange 63000 1000).foldl roundedStep (923263233,831143630) = (928346880,831177029) ∧
    ((primeRange 63000 1000).map Nat.log2).sum = 1395 := by
  decide +kernel

lemma chunk_info_64 : (primeRange 64000 1000).foldl roundedStep (928346880,831177029) = (932675038,831205028) ∧
    ((primeRange 64000 1000).map Nat.log2).sum = 1200 := by
  decide +kernel

end Erdos7SharpRawPrefix
