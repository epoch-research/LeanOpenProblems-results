import Submission.CountThreeOrder

/-! Kernel-checkable finite data for normalized quadrilateral outside graphs.
This module concerns a restricted finite classification, not Spec. -/
namespace Erdos184.QuadrilateralOutsideData

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

def edgeIndex (i j : ℕ) : ℕ :=
  (max i j - 1) * (max i j - 2) / 2 + (min i j - 1)

def adjCode (code i j : ℕ) : Bool :=
  if i = j then false else
  if i = 0 then decide (j ≤ 2) else
  if j = 0 then decide (i ≤ 2) else
  decide (code / 2 ^ edgeIndex i j % 2 = 1)

def degreeCode (code i : ℕ) : ℕ :=
  ((List.range 7).map (fun j => if adjCode code i j then 1 else 0)).sum

def eligible (n code : ℕ) : Bool :=
  (List.range 7).all (fun i =>
    if i < n then decide (2 ≤ degreeCode code i ∧ degreeCode code i ≤ 3)
    else decide (degreeCode code i = 0)) &&
  decide (((List.range 7).map (degreeCode code)).sum = 4*n-8) &&
  (List.range 7).all (fun i => (List.range 7).all (fun j =>
    (List.range 7).all (fun k => !(adjCode code i j && adjCode code j k && adjCode code k i))))

def patterns : ℕ → List ℕ
  | 4 => [6]
  | 5 => [30]
  | 6 => [504, 742, 798]
  | 7 => [14164, 15242, 22188, 23154, 26034, 26988]
  | _ => []

def checkRange (n : ℕ) : ℕ → ℕ → Bool
  | 0, start => !eligible n start || (patterns n).contains start
  | depth+1, start => checkRange n depth start && checkRange n depth (start + 2^depth)

lemma checkRange_sound (n depth start : ℕ) (h : checkRange n depth start = true)
    (i : ℕ) (hi : i < 2^depth) :
    eligible n (start+i) = true → start+i ∈ patterns n := by
  induction depth generalizing start i with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    simp only [Nat.add_zero]
    simp [checkRange] at h
    intro he
    rcases h with h | h
    · rw [h] at he
      contradiction
    · exact h
  | succ depth ih =>
    simp only [checkRange,Bool.and_eq_true] at h
    by_cases hlo : i < 2^depth
    · exact ih start h.1 i hlo
    · have hlt : i - 2^depth < 2^depth := by
        simp only [pow_succ] at hi
        omega
      have hh := ih (start + 2^depth) h.2 (i-2^depth) hlt
      simpa only [Nat.add_assoc,Nat.add_sub_of_le (Nat.le_of_not_gt hlo)] using hh

lemma range_checked_4 : checkRange 4 3 0 = true := by
  decide +kernel

lemma checked_4 (code : Fin 8) : eligible 4 code.val = true → code.val ∈ patterns 4 := by
  simpa only [Nat.zero_add] using checkRange_sound 4 3 0 range_checked_4 code.val code.isLt

lemma range_checked_5 : checkRange 5 6 0 = true := by
  decide +kernel

lemma checked_5 (code : Fin 64) : eligible 5 code.val = true → code.val ∈ patterns 5 := by
  simpa only [Nat.zero_add] using checkRange_sound 5 6 0 range_checked_5 code.val code.isLt

lemma range_checked_6 : checkRange 6 10 0 = true := by
  decide +kernel

lemma checked_6 (code : Fin 1024) : eligible 6 code.val = true → code.val ∈ patterns 6 := by
  simpa only [Nat.zero_add] using checkRange_sound 6 10 0 range_checked_6 code.val code.isLt

def adjCode7 (code i j : ℕ) : Bool :=
  if i = j then false else
  if i = 0 then decide (j = 1 ∨ j = 2) else
  if j = 0 then decide (i = 1 ∨ i = 2) else
  if i = 1 then decide (j = 3 ∨ j = 4) else
  if j = 1 then decide (i = 3 ∨ i = 4) else
  decide (code / 2 ^ edgeIndex (i-1) (j-1) % 2 = 1)

def degreeCode7 (code i : ℕ) : ℕ :=
  ((List.range 7).map (fun j => if adjCode7 code i j then 1 else 0)).sum

def eligible7 (code : ℕ) : Bool :=
  (List.range 6).all (fun i => decide (degreeCode7 code (i+1) = 3)) &&
  (List.range 7).all (fun i => (List.range 7).all (fun j =>
    (List.range 7).all (fun k => !(adjCode7 code i j && adjCode7 code j k && adjCode7 code k i))))

lemma checked_7 : ∀ code : Fin 1024, eligible7 code.val = true → code.val = 504 := by
  decide +kernel

end Erdos184.QuadrilateralOutsideData
