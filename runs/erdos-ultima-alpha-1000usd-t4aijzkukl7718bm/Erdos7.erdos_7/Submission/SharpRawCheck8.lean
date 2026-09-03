import Submission.SharpRawPrefixData
namespace Erdos7SharpRawPrefix
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
open Erdos7No23Sieve
lemma chunk_info_40 : (primeRange 40000 1000).foldl roundedStep (789092232,830024338) = (795547438,830090789) ∧
    ((primeRange 40000 1000).map Nat.log2).sum = 1320 := by
  decide +kernel

lemma chunk_info_41 : (primeRange 41000 1000).foldl roundedStep (795547438,830090789) = (802840450,830164059) ∧
    ((primeRange 41000 1000).map Nat.log2).sum = 1515 := by
  decide +kernel

lemma chunk_info_42 : (primeRange 42000 1000).foldl roundedStep (802840450,830164059) = (810099236,830235282) ∧
    ((primeRange 42000 1000).map Nat.log2).sum = 1530 := by
  decide +kernel

lemma chunk_info_43 : (primeRange 43000 1000).foldl roundedStep (810099236,830235282) = (816054806,830292351) ∧
    ((primeRange 43000 1000).map Nat.log2).sum = 1275 := by
  decide +kernel

lemma chunk_info_44 : (primeRange 44000 1000).foldl roundedStep (816054806,830292351) = (822683628,830354472) ∧
    ((primeRange 44000 1000).map Nat.log2).sum = 1440 := by
  decide +kernel

end Erdos7SharpRawPrefix
