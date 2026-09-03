import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_25 : (primeRange 25000 1000).foldl roundedStep (666022132,828395580) = (675686844,828553514) ∧
    ((primeRange 25000 1000).map Nat.log2).sum = 1372 := by
  decide +kernel

lemma chunk_info_26 : (primeRange 26000 1000).foldl roundedStep (675686844,828553514) = (685410248,828706414) ∧
    ((primeRange 26000 1000).map Nat.log2).sum = 1414 := by
  decide +kernel

lemma chunk_info_27 : (primeRange 27000 1000).foldl roundedStep (685410248,828706414) = (694245171,828840231) ∧
    ((primeRange 27000 1000).map Nat.log2).sum = 1316 := by
  decide +kernel

lemma chunk_info_28 : (primeRange 28000 1000).foldl roundedStep (694245171,828840231) = (703254435,828971992) ∧
    ((primeRange 28000 1000).map Nat.log2).sum = 1372 := by
  decide +kernel

lemma chunk_info_29 : (primeRange 29000 1000).foldl roundedStep (703254435,828971992) = (711536051,829089140) ∧
    ((primeRange 29000 1000).map Nat.log2).sum = 1288 := by
  decide +kernel

end Erdos7SharpRawPrefix
