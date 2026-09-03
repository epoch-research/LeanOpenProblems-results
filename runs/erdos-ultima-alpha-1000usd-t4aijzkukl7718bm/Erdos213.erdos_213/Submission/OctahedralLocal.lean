import Submission.OctahedralColor

set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
namespace Erdos213.OctahedralLocal

def square16 (z : ZMod 16) : Bool := z.val == 0 || z.val == 1 || z.val == 4 || z.val == 9

lemma square16_iff : ∀ z : ZMod 16, square16 z = true ↔ IsSquare z := by
  change ∀ z : ZMod 16, square16 z = true ↔ ∃ r : ZMod 16, z = r*r
  decide

def codeValue (a b c : ZMod 16) (k : Fin 44) : ZMod 16 :=
  (if k.val < 22 then 1 else 2) * forms a b c ⟨k.val%22, Nat.mod_lt _ (by norm_num)⟩

def profile (a b c : ZMod 16) : ℕ :=
  (List.finRange 44).foldl (fun m k => if square16 (codeValue a b c k) then m ||| (2^k.val) else m) 0

def choiceMask (k : Fin 8) : ℕ :=
  2^(1+if k.val.testBit 0 then 0 else 22) +
  2^(2+if k.val.testBit 1 then 0 else 22) +
  2^(3+if k.val.testBit 2 then 0 else 22)

def refinedProfile (a b c : ZMod 16) (k : Fin 8) : ℕ :=
  profile a b c &&& ((2^44-1)-choiceMask k)

set_option maxHeartbeats 10000000 in
private lemma profile_cover_0 : ∀ b c : ZMod 16,
    ((0 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 0 b c q &&& allowedMask k = refinedProfile 0 b c q := by
  decide
run_cmd do IO.println "profile 0 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_1 : ∀ b c : ZMod 16,
    ((1 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 1 b c q &&& allowedMask k = refinedProfile 1 b c q := by
  decide
run_cmd do IO.println "profile 1 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_2 : ∀ b c : ZMod 16,
    ((2 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 2 b c q &&& allowedMask k = refinedProfile 2 b c q := by
  decide
run_cmd do IO.println "profile 2 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_3 : ∀ b c : ZMod 16,
    ((3 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 3 b c q &&& allowedMask k = refinedProfile 3 b c q := by
  decide
run_cmd do IO.println "profile 3 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_4 : ∀ b c : ZMod 16,
    ((4 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 4 b c q &&& allowedMask k = refinedProfile 4 b c q := by
  decide
run_cmd do IO.println "profile 4 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_5 : ∀ b c : ZMod 16,
    ((5 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 5 b c q &&& allowedMask k = refinedProfile 5 b c q := by
  decide
run_cmd do IO.println "profile 5 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_6 : ∀ b c : ZMod 16,
    ((6 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 6 b c q &&& allowedMask k = refinedProfile 6 b c q := by
  decide
run_cmd do IO.println "profile 6 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_7 : ∀ b c : ZMod 16,
    ((7 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 7 b c q &&& allowedMask k = refinedProfile 7 b c q := by
  decide
run_cmd do IO.println "profile 7 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_8 : ∀ b c : ZMod 16,
    ((8 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 8 b c q &&& allowedMask k = refinedProfile 8 b c q := by
  decide
run_cmd do IO.println "profile 8 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_9 : ∀ b c : ZMod 16,
    ((9 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 9 b c q &&& allowedMask k = refinedProfile 9 b c q := by
  decide
run_cmd do IO.println "profile 9 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_10 : ∀ b c : ZMod 16,
    ((10 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 10 b c q &&& allowedMask k = refinedProfile 10 b c q := by
  decide
run_cmd do IO.println "profile 10 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_11 : ∀ b c : ZMod 16,
    ((11 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 11 b c q &&& allowedMask k = refinedProfile 11 b c q := by
  decide
run_cmd do IO.println "profile 11 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_12 : ∀ b c : ZMod 16,
    ((12 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 12 b c q &&& allowedMask k = refinedProfile 12 b c q := by
  decide
run_cmd do IO.println "profile 12 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_13 : ∀ b c : ZMod 16,
    ((13 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 13 b c q &&& allowedMask k = refinedProfile 13 b c q := by
  decide
run_cmd do IO.println "profile 13 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_14 : ∀ b c : ZMod 16,
    ((14 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 14 b c q &&& allowedMask k = refinedProfile 14 b c q := by
  decide
run_cmd do IO.println "profile 14 done"; (← IO.getStdout).flush

set_option maxHeartbeats 10000000 in
private lemma profile_cover_15 : ∀ b c : ZMod 16,
    ((15 : ZMod 16).val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile 15 b c q &&& allowedMask k = refinedProfile 15 b c q := by
  decide
run_cmd do IO.println "profile 15 done"; (← IO.getStdout).flush

lemma profile_cover : ∀ a b c : ZMod 16,
    (a.val%2 = 1 ∨ b.val%2 = 1 ∨ c.val%2 = 1) → ∀ q : Fin 8,
      ∃ k : Fin 16, refinedProfile a b c q &&& allowedMask k = refinedProfile a b c q := by
  intro a
  fin_cases a
  · exact profile_cover_0
  · exact profile_cover_1
  · exact profile_cover_2
  · exact profile_cover_3
  · exact profile_cover_4
  · exact profile_cover_5
  · exact profile_cover_6
  · exact profile_cover_7
  · exact profile_cover_8
  · exact profile_cover_9
  · exact profile_cover_10
  · exact profile_cover_11
  · exact profile_cover_12
  · exact profile_cover_13
  · exact profile_cover_14
  · exact profile_cover_15

#print axioms profile_cover
end Erdos213.OctahedralLocal
