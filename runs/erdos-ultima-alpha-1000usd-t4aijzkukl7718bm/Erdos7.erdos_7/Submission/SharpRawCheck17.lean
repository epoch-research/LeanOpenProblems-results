import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_85 : (primeRange 85000 1000).foldl roundedStep (1020320068,831698144) = (1024132130,831716772) ∧
    ((primeRange 85000 1000).map Nat.log2).sum = 1360 := by
  decide +kernel

lemma chunk_info_86 : (primeRange 86000 1000).foldl roundedStep (1024132130,831716772) = (1028047832,831735684) ∧
    ((primeRange 86000 1000).map Nat.log2).sum = 1408 := by
  decide +kernel

lemma chunk_info_87 : (primeRange 87000 1000).foldl roundedStep (1028047832,831735684) = (1032153146,831755280) ∧
    ((primeRange 87000 1000).map Nat.log2).sum = 1488 := by
  decide +kernel

lemma chunk_info_88 : (primeRange 88000 1000).foldl roundedStep (1032153146,831755280) = (1035480974,831770979) ∧
    ((primeRange 88000 1000).map Nat.log2).sum = 1216 := by
  decide +kernel

lemma chunk_info_89 : (primeRange 89000 1000).foldl roundedStep (1035480974,831770979) = (1039567741,831790055) ∧
    ((primeRange 89000 1000).map Nat.log2).sum = 1504 := by
  decide +kernel

end Erdos7SharpRawPrefix
