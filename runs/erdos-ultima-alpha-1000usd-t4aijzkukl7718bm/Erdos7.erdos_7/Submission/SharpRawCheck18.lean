import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_90 : (primeRange 90000 1000).foldl roundedStep (1039567741,831790055) = (1043409968,831807796) ∧
    ((primeRange 90000 1000).map Nat.log2).sum = 1424 := by
  decide +kernel

lemma chunk_info_91 : (primeRange 91000 1000).foldl roundedStep (1043409968,831807796) = (1047051451,831824421) ∧
    ((primeRange 91000 1000).map Nat.log2).sum = 1360 := by
  decide +kernel

lemma chunk_info_92 : (primeRange 92000 1000).foldl roundedStep (1047051451,831824421) = (1051176583,831843048) ∧
    ((primeRange 92000 1000).map Nat.log2).sum = 1552 := by
  decide +kernel

lemma chunk_info_93 : (primeRange 93000 1000).foldl roundedStep (1051176583,831843048) = (1054808687,831859277) ∧
    ((primeRange 93000 1000).map Nat.log2).sum = 1376 := by
  decide +kernel

lemma chunk_info_94 : (primeRange 94000 1000).foldl roundedStep (1054808687,831859277) = (1058456560,831875404) ∧
    ((primeRange 94000 1000).map Nat.log2).sum = 1392 := by
  decide +kernel

end Erdos7SharpRawPrefix
