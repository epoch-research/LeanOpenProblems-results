import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_65 : (primeRange 65000 1000).foldl roundedStep (932675038,831205028) = (937923119,831238462) ∧
    ((primeRange 65000 1000).map Nat.log2).sum = 1519 := by
  decide +kernel

lemma chunk_info_66 : (primeRange 66000 1000).foldl roundedStep (937923119,831238462) = (942375150,831266393) ∧
    ((primeRange 66000 1000).map Nat.log2).sum = 1344 := by
  decide +kernel

lemma chunk_info_67 : (primeRange 67000 1000).foldl roundedStep (942375150,831266393) = (947572084,831298520) ∧
    ((primeRange 67000 1000).map Nat.log2).sum = 1584 := by
  decide +kernel

lemma chunk_info_68 : (primeRange 68000 1000).foldl roundedStep (947572084,831298520) = (951729918,831323846) ∧
    ((primeRange 68000 1000).map Nat.log2).sum = 1280 := by
  decide +kernel

lemma chunk_info_69 : (primeRange 69000 1000).foldl roundedStep (951729918,831323846) = (955899720,831348891) ∧
    ((primeRange 69000 1000).map Nat.log2).sum = 1296 := by
  decide +kernel

end Erdos7SharpRawPrefix
