import Submission.SmallGraphEncoding
import Submission.CyclePairCertificate

/-! Exact rejection certificates for the normalized triangle outside cases.
This module is finite auxiliary data, not a settlement of Spec. -/
open SimpleGraph
namespace Erdos184.TriangleOutsideData
open SmallGraphEncoding CyclePairCertificate
set_option maxHeartbeats 10000000
set_option maxRecDepth 50000

structure CycleData where
  size : ℕ
  vertex : Fin (size+3) → Fin 6

structure Rejection where
  degree : ℕ
  code : ℕ
  first : CycleData
  second : CycleData

def rejections : Array Rejection :=
  #[{ degree := 1, code := 447, first := { size := 0, vertex := ![1,2,3] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 1, code := 503, first := { size := 0, vertex := ![1,2,3] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 1, code := 509, first := { size := 0, vertex := ![1,2,4] }, second := { size := 0, vertex := ![2,3,5] } },
    { degree := 1, code := 510, first := { size := 0, vertex := ![1,3,4] }, second := { size := 0, vertex := ![2,3,5] } },
    { degree := 1, code := 703, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 759, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 765, first := { size := 1, vertex := ![1,2,3,4] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 766, first := { size := 0, vertex := ![1,3,4] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 831, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 887, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 893, first := { size := 0, vertex := ![1,2,4] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 894, first := { size := 1, vertex := ![1,3,2,4] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 927, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 943, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 951, first := { size := 0, vertex := ![1,2,3] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 1, code := 955, first := { size := 0, vertex := ![1,2,4] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 957, first := { size := 1, vertex := ![1,2,3,4] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 958, first := { size := 1, vertex := ![1,3,2,4] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 983, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 989, first := { size := 1, vertex := ![1,2,3,5] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 990, first := { size := 0, vertex := ![1,3,5] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 999, first := { size := 0, vertex := ![1,2,3] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 1005, first := { size := 0, vertex := ![1,2,5] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 1006, first := { size := 1, vertex := ![1,3,2,5] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 1011, first := { size := 0, vertex := ![1,2,5] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 1013, first := { size := 1, vertex := ![1,2,3,5] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 1014, first := { size := 1, vertex := ![1,3,2,5] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 1017, first := { size := 0, vertex := ![1,2,4] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 1, code := 1018, first := { size := 0, vertex := ![1,3,4] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 1, code := 1020, first := { size := 1, vertex := ![1,4,2,5] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 31, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,3,2,4] } },
    { degree := 2, code := 47, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 55, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![2,3,4] } },
    { degree := 2, code := 59, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 61, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![2,3,4] } },
    { degree := 2, code := 254, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![1,4,2,5] } },
    { degree := 2, code := 375, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,5] } },
    { degree := 2, code := 381, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,4,2,3,5] } },
    { degree := 2, code := 382, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![1,4,3,5] } },
    { degree := 2, code := 431, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 443, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 446, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 2, code := 478, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![1,4,2,5] } },
    { degree := 2, code := 493, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,4,3,2,5] } },
    { degree := 2, code := 494, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![1,4,3,5] } },
    { degree := 2, code := 499, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,4,2,5] } },
    { degree := 2, code := 502, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 2, code := 505, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,4,2,5] } },
    { degree := 2, code := 506, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 0, vertex := ![1,3,5] } },
    { degree := 2, code := 508, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 0, vertex := ![2,3,5] } },
    { degree := 2, code := 631, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,2,4,5] } },
    { degree := 2, code := 637, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 638, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 687, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,2,5,4] } },
    { degree := 2, code := 699, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 702, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 2, code := 734, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![1,4,2,5] } },
    { degree := 2, code := 743, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,3,2,5] } },
    { degree := 2, code := 749, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,4,3,2,5] } },
    { degree := 2, code := 750, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 755, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,4,2,5] } },
    { degree := 2, code := 758, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 2, code := 762, first := { size := 2, vertex := ![0,1,3,4,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 764, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 1, vertex := ![2,3,4,5] } },
    { degree := 2, code := 799, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,3,2,4] } },
    { degree := 2, code := 815, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 823, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![2,3,4] } },
    { degree := 2, code := 827, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 829, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![2,3,4] } },
    { degree := 2, code := 830, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 855, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,2,4,5] } },
    { degree := 2, code := 861, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,4,2,3,5] } },
    { degree := 2, code := 862, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 871, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,3,4,5] } },
    { degree := 2, code := 877, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,4,3,5] } },
    { degree := 2, code := 878, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![1,4,3,5] } },
    { degree := 2, code := 883, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,3,4,5] } },
    { degree := 2, code := 885, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![2,3,4] } },
    { degree := 2, code := 886, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 889, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,4,3,5] } },
    { degree := 2, code := 890, first := { size := 2, vertex := ![0,1,3,4,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 892, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 911, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,2,5,4] } },
    { degree := 2, code := 923, first := { size := 0, vertex := ![0,1,2] }, second := { size := 2, vertex := ![1,3,5,2,4] } },
    { degree := 2, code := 926, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 2, code := 935, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![2,3,4,5] } },
    { degree := 2, code := 939, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,4] } },
    { degree := 2, code := 941, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![2,3,4,5] } },
    { degree := 2, code := 942, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 947, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 2, code := 950, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 2, code := 953, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 2, code := 954, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 956, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 1, vertex := ![2,3,4,5] } },
    { degree := 2, code := 973, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 974, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 979, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![1,3,5] } },
    { degree := 2, code := 982, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 2, code := 986, first := { size := 2, vertex := ![0,1,3,5,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 988, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 0, vertex := ![2,3,5] } },
    { degree := 2, code := 995, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,3,4,5] } },
    { degree := 2, code := 997, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![2,3,4,5] } },
    { degree := 2, code := 998, first := { size := 1, vertex := ![0,1,3,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 1001, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![1,4,3,5] } },
    { degree := 2, code := 1002, first := { size := 2, vertex := ![0,1,3,5,2] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 2, code := 1004, first := { size := 1, vertex := ![0,1,5,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 1009, first := { size := 0, vertex := ![0,1,2] }, second := { size := 1, vertex := ![2,4,3,5] } },
    { degree := 2, code := 1010, first := { size := 1, vertex := ![0,1,5,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 2, code := 1012, first := { size := 1, vertex := ![0,1,5,2] }, second := { size := 0, vertex := ![2,3,4] } },
    { degree := 2, code := 1016, first := { size := 1, vertex := ![0,1,4,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 3, code := 748, first := { size := 0, vertex := ![0,2,3] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 3, code := 754, first := { size := 0, vertex := ![0,1,3] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 3, code := 860, first := { size := 0, vertex := ![0,2,3] }, second := { size := 0, vertex := ![1,4,5] } },
    { degree := 3, code := 881, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![3,4,5] } },
    { degree := 3, code := 922, first := { size := 0, vertex := ![0,1,3] }, second := { size := 0, vertex := ![2,4,5] } },
    { degree := 3, code := 937, first := { size := 0, vertex := ![0,1,2] }, second := { size := 0, vertex := ![3,4,5] } }]

def eligible (d n code : ℕ) : Bool :=
  (List.range 6).all (fun i => if i < n then
    decide (d ≤ degreeCode 6 d code i ∧ degreeCode 6 d code i ≤ 4)
    else decide (degreeCode 6 d code i = 0)) &&
  decide (((List.range 6).map (degreeCode 6 d code)).sum = 4*n-6)

def good (d n code : ℕ) : Bool :=
  decide ((d = 1 ∧ n = 2 ∧ code = 0) ∨
    (d = 1 ∧ n = 5 ∧ code = 63) ∨
    (d = 2 ∧ n = 3 ∧ code = 1) ∨
    (d = 2 ∧ n = 4 ∧ code = 7) ∨
    (d = 2 ∧ n = 5 ∧ code = 62) ∨
    (d = 3 ∧ n = 6 ∧ code = 504))

def rejector (d code : ℕ) : Option Rejection :=
  rejections.toList.find? (fun r => decide (r.degree = d ∧ r.code = code))

def classified (d n code : ℕ) : Bool :=
  !eligible d n code || good d n code || (rejector d code).isSome

def checkRange (d n : ℕ) : ℕ → ℕ → Bool
  | 0, start => classified d n start
  | depth+1, start => checkRange d n depth start && checkRange d n depth (start + 2^depth)

lemma checkRange_sound (d n depth start : ℕ) (h : checkRange d n depth start = true)
    (i : ℕ) (hi : i < 2^depth) : classified d n (start+i) = true := by
  induction depth generalizing start i with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    simpa [checkRange] using h
  | succ depth ih =>
    simp only [checkRange,Bool.and_eq_true] at h
    by_cases hlo : i < 2^depth
    · exact ih start h.1 i hlo
    · have hlt : i - 2^depth < 2^depth := by simp only [pow_succ] at hi; omega
      have hh := ih (start + 2^depth) h.2 (i-2^depth) hlt
      simpa only [Nat.add_assoc,Nat.add_sub_of_le (Nat.le_of_not_gt hlo)] using hh

def checkRejection (r : Rejection) : Bool :=
  decide (Function.Injective r.first.vertex ∧ Function.Injective r.second.vertex ∧
    (∀ i, (graph 6 r.degree r.code).Adj (r.first.vertex i) (r.first.vertex (i+1))) ∧
    (∀ i, (graph 6 r.degree r.code).Adj (r.second.vertex i) (r.second.vertex (i+1))) ∧
    Disjoint (cycleEdges r.first.vertex) (cycleEdges r.second.vertex))

end Erdos184.TriangleOutsideData
