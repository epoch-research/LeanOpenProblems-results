import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_10 : (primeRange 10000 1000).foldl roundedStep (467786023,823097714) = (485861664,823816476) ∧
    ((primeRange 10000 1000).map Nat.log2).sum = 1378 := by
  decide +kernel

lemma chunk_info_11 : (primeRange 11000 1000).foldl roundedStep (485861664,823816476) = (502448988,824417482) ∧
    ((primeRange 11000 1000).map Nat.log2).sum = 1339 := by
  decide +kernel

lemma chunk_info_12 : (primeRange 12000 1000).foldl roundedStep (502448988,824417482) = (519155939,824974797) ∧
    ((primeRange 12000 1000).map Nat.log2).sum = 1417 := by
  decide +kernel

lemma chunk_info_13 : (primeRange 13000 1000).foldl roundedStep (519155939,824974797) = (534529271,825449745) ∧
    ((primeRange 13000 1000).map Nat.log2).sum = 1365 := by
  decide +kernel

lemma chunk_info_14 : (primeRange 14000 1000).foldl roundedStep (534529271,825449745) = (548799383,825859450) ∧
    ((primeRange 14000 1000).map Nat.log2).sum = 1326 := by
  decide +kernel

end Erdos7SharpRawPrefix
