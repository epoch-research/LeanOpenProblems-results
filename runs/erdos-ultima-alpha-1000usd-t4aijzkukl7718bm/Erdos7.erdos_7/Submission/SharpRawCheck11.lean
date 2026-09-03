import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_55 : (primeRange 55000 1000).foldl roundedStep (881294082,830845780) = (886847630,830887507) ∧
    ((primeRange 55000 1000).map Nat.log2).sum = 1395 := by
  decide +kernel

lemma chunk_info_56 : (primeRange 56000 1000).foldl roundedStep (886847630,830887507) = (892691186,830930629) ∧
    ((primeRange 56000 1000).map Nat.log2).sum = 1485 := by
  decide +kernel

lemma chunk_info_57 : (primeRange 57000 1000).foldl roundedStep (892691186,830930629) = (898004955,830969183) ∧
    ((primeRange 57000 1000).map Nat.log2).sum = 1365 := by
  decide +kernel

lemma chunk_info_58 : (primeRange 58000 1000).foldl roundedStep (898004955,830969183) = (903202732,831006263) ∧
    ((primeRange 58000 1000).map Nat.log2).sum = 1350 := by
  decide +kernel

lemma chunk_info_59 : (primeRange 59000 1000).foldl roundedStep (903202732,831006263) = (908573340,831043947) ∧
    ((primeRange 59000 1000).map Nat.log2).sum = 1410 := by
  decide +kernel

end Erdos7SharpRawPrefix
