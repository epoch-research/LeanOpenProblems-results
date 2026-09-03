import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_20 : (primeRange 20000 1000).foldl roundedStep (612492348,827396111) = (623581399,827621788) ∧
    ((primeRange 20000 1000).map Nat.log2).sum = 1372 := by
  decide +kernel

lemma chunk_info_21 : (primeRange 21000 1000).foldl roundedStep (623581399,827621788) = (635004423,827843405) ∧
    ((primeRange 21000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

lemma chunk_info_22 : (primeRange 22000 1000).foldl roundedStep (635004423,827843405) = (645688371,828041546) ∧
    ((primeRange 22000 1000).map Nat.log2).sum = 1400 := by
  decide +kernel

lemma chunk_info_23 : (primeRange 23000 1000).foldl roundedStep (645688371,828041546) = (656498381,828233376) ∧
    ((primeRange 23000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

lemma chunk_info_24 : (primeRange 24000 1000).foldl roundedStep (656498381,828233376) = (666022132,828395580) ∧
    ((primeRange 24000 1000).map Nat.log2).sum = 1316 := by
  decide +kernel

end Erdos7SharpRawPrefix
