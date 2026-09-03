import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_75 : (primeRange 75000 1000).foldl roundedStep (978839435,831481121) = (983273475,831505634) ∧
    ((primeRange 75000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

lemma chunk_info_76 : (primeRange 76000 1000).foldl roundedStep (983273475,831505634) = (987282198,831527511) ∧
    ((primeRange 76000 1000).map Nat.log2).sum = 1328 := by
  decide +kernel

lemma chunk_info_77 : (primeRange 77000 1000).foldl roundedStep (987282198,831527511) = (991831212,831552018) ∧
    ((primeRange 77000 1000).map Nat.log2).sum = 1520 := by
  decide +kernel

lemma chunk_info_78 : (primeRange 78000 1000).foldl roundedStep (991831212,831552018) = (995819094,831573224) ∧
    ((primeRange 78000 1000).map Nat.log2).sum = 1344 := by
  decide +kernel

lemma chunk_info_79 : (primeRange 79000 1000).foldl roundedStep (995819094,831573224) = (1000101383,831595712) ∧
    ((primeRange 79000 1000).map Nat.log2).sum = 1456 := by
  decide +kernel

end Erdos7SharpRawPrefix
