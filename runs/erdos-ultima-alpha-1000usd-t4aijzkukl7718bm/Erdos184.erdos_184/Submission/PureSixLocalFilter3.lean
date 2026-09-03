import Submission.PureSixRowModel3
import Submission.FiniteCaseLookup
import Submission.FiniteIntervals
import Mathlib.Data.Finset.Basic

/-! Pure projected-word filters and a factored enumeration interface.
Completeness of the output lookup is NOT asserted in this base module. -/
namespace Erdos184Work.PureSixLocalFilter3
open FiniteCaseLookup PureSixRowModel3
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSectionVars false
def output : Table ℕ := .empty
abbrev SmallKeys0 := Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 3
def enc0_0 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,12,9,11,3,7,1,5,6,2,4,10,4,8,6,8,2,10,5,9,12,10,8,3,1,4,2,11,7,7,11,3,5,9,6,12,1]
def projRow0_0 (q : Fin 60) : Fin 12 := ⟨(enc0_0 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc0_1 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,12,9,11,3,7,1,5,6,2,4,10,4,8,6,8,2,10,5,9,12,10,8,3,1,4,2,11,7,7,11,3,5,9,6,12,1]
def projRow0_1 (q : Fin 60) : Fin 12 := ⟨(enc0_1 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc0_2 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,12,9,11,3,7,1,5,6,2,4,10,4,8,6,8,2,10,5,9,12,10,8,3,1,4,2,11,7,7,11,3,5,9,6,12,1]
def projRow0_2 (q : Fin 60) : Fin 12 := ⟨(enc0_2 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc0_3 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,12,9,11,3,7,1,5,6,2,4,10,4,8,6,8,2,10,5,9,12,10,8,3,1,4,2,11,7,7,11,3,5,9,6,12,1]
def projRow0_3 (q : Fin 60) : Fin 12 := ⟨(enc0_3 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc0_4 : Fin 60 → ℕ := ![1,2,3,2,3,1,2,1,3,1,3,2,2,3,1,3,1,2,1,3,2,3,2,1,1,2,3,2,3,1,1,2,1,2,3,2,3,2,3,1,3,1,2,1,3,3,2,1,2,1,3,3,3,3,2,1,2,2,1,1]
def projRow0_4 (q : Fin 60) : Fin 3 := ⟨(enc0_4 q - 1) % 3,Nat.mod_lt _ (by decide)⟩
def project0 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : SmallKeys0 := (projRow0_0 q2,projRow0_1 q3,projRow0_2 q4,projRow0_3 q5,projRow0_4 q1)
def smallKey0 (q : SmallKeys0) : ℕ := 5184 * q.1.val + 432 * q.2.1.val + 36 * q.2.2.1.val + 3 * q.2.2.2.1.val + 1 * q.2.2.2.2.val
def allowed0 (t : Fin 24) : SmallKeys0 := (if t.val < 12 then (if t.val < 6 then (if t.val < 3 then (if t.val < 1 then (6,9,6,9,0) else (if t.val < 2 then (6,9,6,9,1) else (6,9,6,9,2))) else (if t.val < 4 then (6,9,10,7,0) else (if t.val < 5 then (6,9,10,7,1) else (6,9,10,7,2)))) else (if t.val < 9 then (if t.val < 7 then (7,10,6,9,0) else (if t.val < 8 then (7,10,6,9,1) else (7,10,6,9,2))) else (if t.val < 10 then (7,10,10,7,0) else (if t.val < 11 then (7,10,10,7,1) else (7,10,10,7,2))))) else (if t.val < 18 then (if t.val < 15 then (if t.val < 13 then (9,6,7,10,0) else (if t.val < 14 then (9,6,7,10,1) else (9,6,7,10,2))) else (if t.val < 16 then (9,6,9,6,0) else (if t.val < 17 then (9,6,9,6,1) else (9,6,9,6,2)))) else (if t.val < 21 then (if t.val < 19 then (10,7,7,10,0) else (if t.val < 20 then (10,7,7,10,1) else (10,7,7,10,2))) else (if t.val < 22 then (10,7,9,6,0) else (if t.val < 23 then (10,7,9,6,1) else (10,7,9,6,2))))))
def lookup0 : Table (Fin 24) := (.branch 49530 (.branch 40851 (.branch 35373 (.branch 35236 (.entry 35235 0) (.branch 35237 (.entry 35236 1) (.entry 35237 2))) (.branch 35374 (.entry 35373 3) (.branch 35375 (.entry 35374 4) (.entry 35375 5)))) (.branch 40989 (.branch 40852 (.entry 40851 6) (.branch 40853 (.entry 40852 7) (.entry 40853 8))) (.branch 40990 (.entry 40989 9) (.branch 40991 (.entry 40990 10) (.entry 40991 11))))) (.branch 55146 (.branch 49590 (.branch 49531 (.entry 49530 12) (.branch 49532 (.entry 49531 13) (.entry 49532 14))) (.branch 49591 (.entry 49590 15) (.branch 49592 (.entry 49591 16) (.entry 49592 17)))) (.branch 55206 (.branch 55147 (.entry 55146 18) (.branch 55148 (.entry 55147 19) (.entry 55148 20))) (.branch 55207 (.entry 55206 21) (.branch 55208 (.entry 55207 22) (.entry 55208 23))))))
lemma correct0 : Table.Correct (smallKey0 ∘ allowed0) lookup0 := by decide +kernel
def Test0 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := (lookup0.lookup (smallKey0 (project0 q0 q1 q2 q3 q4 q5))).isSome = true
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Test0 q0 q1 q2 q3 q4 q5) := inferInstanceAs (Decidable (_ = true))
def goodCodes0 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def encode0 (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 5184 * ((q.1 - 1) % 12) + 432 * ((q.2.1 - 1) % 12) + 36 * ((q.2.2.1 - 1) % 12) + 3 * ((q.2.2.2.1 - 1) % 12) + 1 * ((q.2.2.2.2 - 1) % 3)
lemma forward0 : ∀ q ∈ goodCodes0, (lookup0.lookup (encode0 q)).isSome = true := by decide +kernel
abbrev SmallKeys1 := Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 3
def enc1_0 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
def projRow1_0 (q : Fin 60) : Fin 12 := ⟨(enc1_0 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc1_1 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
def projRow1_1 (q : Fin 60) : Fin 12 := ⟨(enc1_1 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc1_2 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
def projRow1_2 (q : Fin 60) : Fin 12 := ⟨(enc1_2 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc1_3 : Fin 60 → ℕ := ![1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,3,7,9,11,12,1,3,1,3,7,9,7,9,11,12,11,12,6,5,8,10,6,5,6,5,8,8,10,10,4,2,4,4,2,2]
def projRow1_3 (q : Fin 60) : Fin 12 := ⟨(enc1_3 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc1_4 : Fin 60 → ℕ := ![1,2,3,2,3,1,2,1,3,1,3,2,2,3,1,3,1,2,1,3,2,3,2,1,1,2,3,2,3,1,1,2,1,2,3,2,3,2,3,1,3,1,2,1,3,3,2,1,2,1,3,3,3,3,2,1,2,2,1,1]
def projRow1_4 (q : Fin 60) : Fin 3 := ⟨(enc1_4 q - 1) % 3,Nat.mod_lt _ (by decide)⟩
def project1 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : SmallKeys1 := (projRow1_0 q2,projRow1_1 q3,projRow1_2 q4,projRow1_3 q5,projRow1_4 q0)
def smallKey1 (q : SmallKeys1) : ℕ := 5184 * q.1.val + 432 * q.2.1.val + 36 * q.2.2.1.val + 3 * q.2.2.2.1.val + 1 * q.2.2.2.2.val
def allowed1 (t : Fin 24) : SmallKeys1 := (if t.val < 12 then (if t.val < 6 then (if t.val < 3 then (if t.val < 1 then (6,9,6,9,0) else (if t.val < 2 then (6,9,6,9,1) else (6,9,6,9,2))) else (if t.val < 4 then (6,9,10,7,0) else (if t.val < 5 then (6,9,10,7,1) else (6,9,10,7,2)))) else (if t.val < 9 then (if t.val < 7 then (7,10,6,9,0) else (if t.val < 8 then (7,10,6,9,1) else (7,10,6,9,2))) else (if t.val < 10 then (7,10,10,7,0) else (if t.val < 11 then (7,10,10,7,1) else (7,10,10,7,2))))) else (if t.val < 18 then (if t.val < 15 then (if t.val < 13 then (9,6,7,10,0) else (if t.val < 14 then (9,6,7,10,1) else (9,6,7,10,2))) else (if t.val < 16 then (9,6,9,6,0) else (if t.val < 17 then (9,6,9,6,1) else (9,6,9,6,2)))) else (if t.val < 21 then (if t.val < 19 then (10,7,7,10,0) else (if t.val < 20 then (10,7,7,10,1) else (10,7,7,10,2))) else (if t.val < 22 then (10,7,9,6,0) else (if t.val < 23 then (10,7,9,6,1) else (10,7,9,6,2))))))
def lookup1 : Table (Fin 24) := (.branch 49530 (.branch 40851 (.branch 35373 (.branch 35236 (.entry 35235 0) (.branch 35237 (.entry 35236 1) (.entry 35237 2))) (.branch 35374 (.entry 35373 3) (.branch 35375 (.entry 35374 4) (.entry 35375 5)))) (.branch 40989 (.branch 40852 (.entry 40851 6) (.branch 40853 (.entry 40852 7) (.entry 40853 8))) (.branch 40990 (.entry 40989 9) (.branch 40991 (.entry 40990 10) (.entry 40991 11))))) (.branch 55146 (.branch 49590 (.branch 49531 (.entry 49530 12) (.branch 49532 (.entry 49531 13) (.entry 49532 14))) (.branch 49591 (.entry 49590 15) (.branch 49592 (.entry 49591 16) (.entry 49592 17)))) (.branch 55206 (.branch 55147 (.entry 55146 18) (.branch 55148 (.entry 55147 19) (.entry 55148 20))) (.branch 55207 (.entry 55206 21) (.branch 55208 (.entry 55207 22) (.entry 55208 23))))))
lemma correct1 : Table.Correct (smallKey1 ∘ allowed1) lookup1 := by decide +kernel
def Test1 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := (lookup1.lookup (smallKey1 (project1 q0 q1 q2 q3 q4 q5))).isSome = true
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Test1 q0 q1 q2 q3 q4 q5) := inferInstanceAs (Decidable (_ = true))
def goodCodes1 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def encode1 (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 5184 * ((q.1 - 1) % 12) + 432 * ((q.2.1 - 1) % 12) + 36 * ((q.2.2.1 - 1) % 12) + 3 * ((q.2.2.2.1 - 1) % 12) + 1 * ((q.2.2.2.2 - 1) % 3)
lemma forward1 : ∀ q ∈ goodCodes1, (lookup1.lookup (encode1 q)).isSome = true := by decide +kernel
abbrev SmallKeys2 := Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 3
def enc2_0 : Fin 60 → ℕ := ![5,6,2,1,4,3,5,6,5,5,6,6,2,1,2,2,1,1,4,3,4,4,3,3,5,6,2,1,4,3,12,9,11,7,8,7,10,9,10,11,8,12,12,9,12,9,12,9,11,7,11,11,7,7,8,8,8,10,10,10]
def projRow2_0 (q : Fin 60) : Fin 12 := ⟨(enc2_0 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc2_1 : Fin 60 → ℕ := ![5,6,2,1,4,3,5,6,5,5,6,6,2,1,2,2,1,1,4,3,4,4,3,3,5,6,2,1,4,3,12,9,11,7,8,7,10,9,10,11,8,12,12,9,12,9,12,9,11,7,11,11,7,7,8,8,8,10,10,10]
def projRow2_1 (q : Fin 60) : Fin 12 := ⟨(enc2_1 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc2_2 : Fin 60 → ℕ := ![5,6,2,1,4,3,5,6,5,5,6,6,2,1,2,2,1,1,4,3,4,4,3,3,5,6,2,1,4,3,12,9,11,7,8,7,10,9,10,11,8,12,12,9,12,9,12,9,11,7,11,11,7,7,8,8,8,10,10,10]
def projRow2_2 (q : Fin 60) : Fin 12 := ⟨(enc2_2 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc2_3 : Fin 60 → ℕ := ![5,6,2,1,4,3,5,6,5,5,6,6,2,1,2,2,1,1,4,3,4,4,3,3,5,6,2,1,4,3,12,9,11,7,8,7,10,9,10,11,8,12,12,9,12,9,12,9,11,7,11,11,7,7,8,8,8,10,10,10]
def projRow2_3 (q : Fin 60) : Fin 12 := ⟨(enc2_3 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc2_4 : Fin 60 → ℕ := ![1,2,1,1,2,2,1,2,1,1,2,2,1,1,1,1,1,1,2,2,2,2,2,2,1,2,1,1,2,2,1,2,3,3,3,3,3,2,3,3,3,1,1,2,1,2,1,2,3,3,3,3,3,3,3,3,3,3,3,3]
def projRow2_4 (q : Fin 60) : Fin 3 := ⟨(enc2_4 q - 1) % 3,Nat.mod_lt _ (by decide)⟩
def project2 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : SmallKeys2 := (projRow2_0 q0,projRow2_1 q1,projRow2_2 q4,projRow2_3 q5,projRow2_4 q3)
def smallKey2 (q : SmallKeys2) : ℕ := 5184 * q.1.val + 432 * q.2.1.val + 36 * q.2.2.1.val + 3 * q.2.2.2.1.val + 1 * q.2.2.2.2.val
def allowed2 (t : Fin 24) : SmallKeys2 := (if t.val < 12 then (if t.val < 6 then (if t.val < 3 then (if t.val < 1 then (6,9,6,9,0) else (if t.val < 2 then (6,9,6,9,1) else (6,9,6,9,2))) else (if t.val < 4 then (6,9,10,7,0) else (if t.val < 5 then (6,9,10,7,1) else (6,9,10,7,2)))) else (if t.val < 9 then (if t.val < 7 then (7,10,6,9,0) else (if t.val < 8 then (7,10,6,9,1) else (7,10,6,9,2))) else (if t.val < 10 then (7,10,10,7,0) else (if t.val < 11 then (7,10,10,7,1) else (7,10,10,7,2))))) else (if t.val < 18 then (if t.val < 15 then (if t.val < 13 then (9,6,7,10,0) else (if t.val < 14 then (9,6,7,10,1) else (9,6,7,10,2))) else (if t.val < 16 then (9,6,9,6,0) else (if t.val < 17 then (9,6,9,6,1) else (9,6,9,6,2)))) else (if t.val < 21 then (if t.val < 19 then (10,7,7,10,0) else (if t.val < 20 then (10,7,7,10,1) else (10,7,7,10,2))) else (if t.val < 22 then (10,7,9,6,0) else (if t.val < 23 then (10,7,9,6,1) else (10,7,9,6,2))))))
def lookup2 : Table (Fin 24) := (.branch 49530 (.branch 40851 (.branch 35373 (.branch 35236 (.entry 35235 0) (.branch 35237 (.entry 35236 1) (.entry 35237 2))) (.branch 35374 (.entry 35373 3) (.branch 35375 (.entry 35374 4) (.entry 35375 5)))) (.branch 40989 (.branch 40852 (.entry 40851 6) (.branch 40853 (.entry 40852 7) (.entry 40853 8))) (.branch 40990 (.entry 40989 9) (.branch 40991 (.entry 40990 10) (.entry 40991 11))))) (.branch 55146 (.branch 49590 (.branch 49531 (.entry 49530 12) (.branch 49532 (.entry 49531 13) (.entry 49532 14))) (.branch 49591 (.entry 49590 15) (.branch 49592 (.entry 49591 16) (.entry 49592 17)))) (.branch 55206 (.branch 55147 (.entry 55146 18) (.branch 55148 (.entry 55147 19) (.entry 55148 20))) (.branch 55207 (.entry 55206 21) (.branch 55208 (.entry 55207 22) (.entry 55208 23))))))
lemma correct2 : Table.Correct (smallKey2 ∘ allowed2) lookup2 := by decide +kernel
def Test2 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := (lookup2.lookup (smallKey2 (project2 q0 q1 q2 q3 q4 q5))).isSome = true
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Test2 q0 q1 q2 q3 q4 q5) := inferInstanceAs (Decidable (_ = true))
def goodCodes2 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def encode2 (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 5184 * ((q.1 - 1) % 12) + 432 * ((q.2.1 - 1) % 12) + 36 * ((q.2.2.1 - 1) % 12) + 3 * ((q.2.2.2.1 - 1) % 12) + 1 * ((q.2.2.2.2 - 1) % 3)
lemma forward2 : ∀ q ∈ goodCodes2, (lookup2.lookup (encode2 q)).isSome = true := by decide +kernel
abbrev SmallKeys3 := Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 3
def enc3_0 : Fin 60 → ℕ := ![5,6,5,5,6,6,5,6,2,1,4,3,2,2,2,1,1,1,4,4,4,3,3,3,12,9,12,12,9,9,12,9,11,7,11,11,11,3,7,7,7,1,5,6,2,4,12,9,11,7,8,10,10,8,8,8,10,10,8,10]
def projRow3_0 (q : Fin 60) : Fin 12 := ⟨(enc3_0 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc3_1 : Fin 60 → ℕ := ![5,6,5,5,6,6,5,6,2,1,4,3,2,2,2,1,1,1,4,4,4,3,3,3,12,9,12,12,9,9,12,9,11,7,11,11,11,3,7,7,7,1,5,6,2,4,12,9,11,7,8,10,10,8,8,8,10,10,8,10]
def projRow3_1 (q : Fin 60) : Fin 12 := ⟨(enc3_1 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc3_2 : Fin 60 → ℕ := ![5,6,5,5,6,6,5,6,2,1,4,3,2,2,2,1,1,1,4,4,4,3,3,3,12,9,12,12,9,9,12,9,11,7,11,11,11,3,7,7,7,1,5,6,2,4,12,9,11,7,8,10,10,8,8,8,10,10,8,10]
def projRow3_2 (q : Fin 60) : Fin 12 := ⟨(enc3_2 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc3_3 : Fin 60 → ℕ := ![5,6,5,5,6,6,5,6,2,1,4,3,2,2,2,1,1,1,4,4,4,3,3,3,12,9,12,12,9,9,12,9,11,7,11,11,11,3,7,7,7,1,5,6,2,4,12,9,11,7,8,10,10,8,8,8,10,10,8,10]
def projRow3_3 (q : Fin 60) : Fin 12 := ⟨(enc3_3 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc3_4 : Fin 60 → ℕ := ![1,2,1,1,2,2,1,2,1,1,2,2,1,1,1,1,1,1,2,2,2,2,2,2,1,2,1,1,2,2,1,2,3,3,3,3,3,2,3,3,3,1,1,2,1,2,1,2,3,3,3,3,3,3,3,3,3,3,3,3]
def projRow3_4 (q : Fin 60) : Fin 3 := ⟨(enc3_4 q - 1) % 3,Nat.mod_lt _ (by decide)⟩
def project3 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : SmallKeys3 := (projRow3_0 q0,projRow3_1 q1,projRow3_2 q4,projRow3_3 q5,projRow3_4 q2)
def smallKey3 (q : SmallKeys3) : ℕ := 5184 * q.1.val + 432 * q.2.1.val + 36 * q.2.2.1.val + 3 * q.2.2.2.1.val + 1 * q.2.2.2.2.val
def allowed3 (t : Fin 24) : SmallKeys3 := (if t.val < 12 then (if t.val < 6 then (if t.val < 3 then (if t.val < 1 then (6,9,6,9,0) else (if t.val < 2 then (6,9,6,9,1) else (6,9,6,9,2))) else (if t.val < 4 then (6,9,10,7,0) else (if t.val < 5 then (6,9,10,7,1) else (6,9,10,7,2)))) else (if t.val < 9 then (if t.val < 7 then (7,10,6,9,0) else (if t.val < 8 then (7,10,6,9,1) else (7,10,6,9,2))) else (if t.val < 10 then (7,10,10,7,0) else (if t.val < 11 then (7,10,10,7,1) else (7,10,10,7,2))))) else (if t.val < 18 then (if t.val < 15 then (if t.val < 13 then (9,6,7,10,0) else (if t.val < 14 then (9,6,7,10,1) else (9,6,7,10,2))) else (if t.val < 16 then (9,6,9,6,0) else (if t.val < 17 then (9,6,9,6,1) else (9,6,9,6,2)))) else (if t.val < 21 then (if t.val < 19 then (10,7,7,10,0) else (if t.val < 20 then (10,7,7,10,1) else (10,7,7,10,2))) else (if t.val < 22 then (10,7,9,6,0) else (if t.val < 23 then (10,7,9,6,1) else (10,7,9,6,2))))))
def lookup3 : Table (Fin 24) := (.branch 49530 (.branch 40851 (.branch 35373 (.branch 35236 (.entry 35235 0) (.branch 35237 (.entry 35236 1) (.entry 35237 2))) (.branch 35374 (.entry 35373 3) (.branch 35375 (.entry 35374 4) (.entry 35375 5)))) (.branch 40989 (.branch 40852 (.entry 40851 6) (.branch 40853 (.entry 40852 7) (.entry 40853 8))) (.branch 40990 (.entry 40989 9) (.branch 40991 (.entry 40990 10) (.entry 40991 11))))) (.branch 55146 (.branch 49590 (.branch 49531 (.entry 49530 12) (.branch 49532 (.entry 49531 13) (.entry 49532 14))) (.branch 49591 (.entry 49590 15) (.branch 49592 (.entry 49591 16) (.entry 49592 17)))) (.branch 55206 (.branch 55147 (.entry 55146 18) (.branch 55148 (.entry 55147 19) (.entry 55148 20))) (.branch 55207 (.entry 55206 21) (.branch 55208 (.entry 55207 22) (.entry 55208 23))))))
lemma correct3 : Table.Correct (smallKey3 ∘ allowed3) lookup3 := by decide +kernel
def Test3 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := (lookup3.lookup (smallKey3 (project3 q0 q1 q2 q3 q4 q5))).isSome = true
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Test3 q0 q1 q2 q3 q4 q5) := inferInstanceAs (Decidable (_ = true))
def goodCodes3 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def encode3 (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 5184 * ((q.1 - 1) % 12) + 432 * ((q.2.1 - 1) % 12) + 36 * ((q.2.2.1 - 1) % 12) + 3 * ((q.2.2.2.1 - 1) % 12) + 1 * ((q.2.2.2.2 - 1) % 3)
lemma forward3 : ∀ q ∈ goodCodes3, (lookup3.lookup (encode3 q)).isSome = true := by decide +kernel
abbrev SmallKeys4 := Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 3
def enc4_0 : Fin 60 → ℕ := ![1,1,1,2,2,2,3,3,3,4,4,4,1,2,3,4,5,6,5,5,6,6,5,6,7,7,7,8,8,8,9,9,9,6,7,8,9,10,10,10,4,10,11,11,11,10,12,12,12,5,11,12,8,2,1,3,7,9,11,12]
def projRow4_0 (q : Fin 60) : Fin 12 := ⟨(enc4_0 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc4_1 : Fin 60 → ℕ := ![1,1,1,2,2,2,3,3,3,4,4,4,1,2,3,4,5,6,5,5,6,6,5,6,7,7,7,8,8,8,9,9,9,6,7,8,9,10,10,10,4,10,11,11,11,10,12,12,12,5,11,12,8,2,1,3,7,9,11,12]
def projRow4_1 (q : Fin 60) : Fin 12 := ⟨(enc4_1 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc4_2 : Fin 60 → ℕ := ![1,1,1,2,2,2,3,3,3,4,4,4,1,2,3,4,5,6,5,5,6,6,5,6,7,7,7,8,8,8,9,9,9,6,7,8,9,10,10,10,4,10,11,11,11,10,12,12,12,5,11,12,8,2,1,3,7,9,11,12]
def projRow4_2 (q : Fin 60) : Fin 12 := ⟨(enc4_2 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc4_3 : Fin 60 → ℕ := ![1,1,1,2,2,2,3,3,3,4,4,4,1,2,3,4,5,6,5,5,6,6,5,6,7,7,7,8,8,8,9,9,9,6,7,8,9,10,10,10,4,10,11,11,11,10,12,12,12,5,11,12,8,2,1,3,7,9,11,12]
def projRow4_3 (q : Fin 60) : Fin 12 := ⟨(enc4_3 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc4_4 : Fin 60 → ℕ := ![1,1,1,1,1,1,2,2,2,2,2,2,1,1,2,2,1,2,1,1,2,2,1,2,3,3,3,3,3,3,2,2,2,2,3,3,2,3,3,3,2,3,3,3,3,3,1,1,1,1,3,1,3,1,1,2,3,2,3,1]
def projRow4_4 (q : Fin 60) : Fin 3 := ⟨(enc4_4 q - 1) % 3,Nat.mod_lt _ (by decide)⟩
def project4 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : SmallKeys4 := (projRow4_0 q0,projRow4_1 q1,projRow4_2 q2,projRow4_3 q3,projRow4_4 q5)
def smallKey4 (q : SmallKeys4) : ℕ := 5184 * q.1.val + 432 * q.2.1.val + 36 * q.2.2.1.val + 3 * q.2.2.2.1.val + 1 * q.2.2.2.2.val
def allowed4 (t : Fin 24) : SmallKeys4 := (if t.val < 12 then (if t.val < 6 then (if t.val < 3 then (if t.val < 1 then (6,9,6,9,0) else (if t.val < 2 then (6,9,6,9,1) else (6,9,6,9,2))) else (if t.val < 4 then (6,9,10,7,0) else (if t.val < 5 then (6,9,10,7,1) else (6,9,10,7,2)))) else (if t.val < 9 then (if t.val < 7 then (7,10,6,9,0) else (if t.val < 8 then (7,10,6,9,1) else (7,10,6,9,2))) else (if t.val < 10 then (7,10,10,7,0) else (if t.val < 11 then (7,10,10,7,1) else (7,10,10,7,2))))) else (if t.val < 18 then (if t.val < 15 then (if t.val < 13 then (9,6,7,10,0) else (if t.val < 14 then (9,6,7,10,1) else (9,6,7,10,2))) else (if t.val < 16 then (9,6,9,6,0) else (if t.val < 17 then (9,6,9,6,1) else (9,6,9,6,2)))) else (if t.val < 21 then (if t.val < 19 then (10,7,7,10,0) else (if t.val < 20 then (10,7,7,10,1) else (10,7,7,10,2))) else (if t.val < 22 then (10,7,9,6,0) else (if t.val < 23 then (10,7,9,6,1) else (10,7,9,6,2))))))
def lookup4 : Table (Fin 24) := (.branch 49530 (.branch 40851 (.branch 35373 (.branch 35236 (.entry 35235 0) (.branch 35237 (.entry 35236 1) (.entry 35237 2))) (.branch 35374 (.entry 35373 3) (.branch 35375 (.entry 35374 4) (.entry 35375 5)))) (.branch 40989 (.branch 40852 (.entry 40851 6) (.branch 40853 (.entry 40852 7) (.entry 40853 8))) (.branch 40990 (.entry 40989 9) (.branch 40991 (.entry 40990 10) (.entry 40991 11))))) (.branch 55146 (.branch 49590 (.branch 49531 (.entry 49530 12) (.branch 49532 (.entry 49531 13) (.entry 49532 14))) (.branch 49591 (.entry 49590 15) (.branch 49592 (.entry 49591 16) (.entry 49592 17)))) (.branch 55206 (.branch 55147 (.entry 55146 18) (.branch 55148 (.entry 55147 19) (.entry 55148 20))) (.branch 55207 (.entry 55206 21) (.branch 55208 (.entry 55207 22) (.entry 55208 23))))))
lemma correct4 : Table.Correct (smallKey4 ∘ allowed4) lookup4 := by decide +kernel
def Test4 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := (lookup4.lookup (smallKey4 (project4 q0 q1 q2 q3 q4 q5))).isSome = true
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Test4 q0 q1 q2 q3 q4 q5) := inferInstanceAs (Decidable (_ = true))
def goodCodes4 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def encode4 (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 5184 * ((q.1 - 1) % 12) + 432 * ((q.2.1 - 1) % 12) + 36 * ((q.2.2.1 - 1) % 12) + 3 * ((q.2.2.2.1 - 1) % 12) + 1 * ((q.2.2.2.2 - 1) % 3)
lemma forward4 : ∀ q ∈ goodCodes4, (lookup4.lookup (encode4 q)).isSome = true := by decide +kernel
abbrev SmallKeys5 := Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 3
def enc5_0 : Fin 60 → ℕ := ![1,1,2,2,1,2,3,3,4,4,3,4,5,5,6,6,5,6,1,2,3,4,5,6,7,7,8,8,7,8,9,9,6,9,10,10,4,10,7,8,9,10,11,11,10,11,12,12,5,12,8,2,11,12,12,9,11,3,7,1]
def projRow5_0 (q : Fin 60) : Fin 12 := ⟨(enc5_0 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc5_1 : Fin 60 → ℕ := ![1,1,2,2,1,2,3,3,4,4,3,4,5,5,6,6,5,6,1,2,3,4,5,6,7,7,8,8,7,8,9,9,6,9,10,10,4,10,7,8,9,10,11,11,10,11,12,12,5,12,8,2,11,12,12,9,11,3,7,1]
def projRow5_1 (q : Fin 60) : Fin 12 := ⟨(enc5_1 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc5_2 : Fin 60 → ℕ := ![1,1,2,2,1,2,3,3,4,4,3,4,5,5,6,6,5,6,1,2,3,4,5,6,7,7,8,8,7,8,9,9,6,9,10,10,4,10,7,8,9,10,11,11,10,11,12,12,5,12,8,2,11,12,12,9,11,3,7,1]
def projRow5_2 (q : Fin 60) : Fin 12 := ⟨(enc5_2 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc5_3 : Fin 60 → ℕ := ![1,1,2,2,1,2,3,3,4,4,3,4,5,5,6,6,5,6,1,2,3,4,5,6,7,7,8,8,7,8,9,9,6,9,10,10,4,10,7,8,9,10,11,11,10,11,12,12,5,12,8,2,11,12,12,9,11,3,7,1]
def projRow5_3 (q : Fin 60) : Fin 12 := ⟨(enc5_3 q - 1) % 12,Nat.mod_lt _ (by decide)⟩
def enc5_4 : Fin 60 → ℕ := ![1,1,1,1,1,1,2,2,2,2,2,2,1,1,2,2,1,2,1,1,2,2,1,2,3,3,3,3,3,3,2,2,2,2,3,3,2,3,3,3,2,3,3,3,3,3,1,1,1,1,3,1,3,1,1,2,3,2,3,1]
def projRow5_4 (q : Fin 60) : Fin 3 := ⟨(enc5_4 q - 1) % 3,Nat.mod_lt _ (by decide)⟩
def project5 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : SmallKeys5 := (projRow5_0 q0,projRow5_1 q1,projRow5_2 q2,projRow5_3 q3,projRow5_4 q4)
def smallKey5 (q : SmallKeys5) : ℕ := 5184 * q.1.val + 432 * q.2.1.val + 36 * q.2.2.1.val + 3 * q.2.2.2.1.val + 1 * q.2.2.2.2.val
def allowed5 (t : Fin 24) : SmallKeys5 := (if t.val < 12 then (if t.val < 6 then (if t.val < 3 then (if t.val < 1 then (6,9,6,9,0) else (if t.val < 2 then (6,9,6,9,1) else (6,9,6,9,2))) else (if t.val < 4 then (6,9,10,7,0) else (if t.val < 5 then (6,9,10,7,1) else (6,9,10,7,2)))) else (if t.val < 9 then (if t.val < 7 then (7,10,6,9,0) else (if t.val < 8 then (7,10,6,9,1) else (7,10,6,9,2))) else (if t.val < 10 then (7,10,10,7,0) else (if t.val < 11 then (7,10,10,7,1) else (7,10,10,7,2))))) else (if t.val < 18 then (if t.val < 15 then (if t.val < 13 then (9,6,7,10,0) else (if t.val < 14 then (9,6,7,10,1) else (9,6,7,10,2))) else (if t.val < 16 then (9,6,9,6,0) else (if t.val < 17 then (9,6,9,6,1) else (9,6,9,6,2)))) else (if t.val < 21 then (if t.val < 19 then (10,7,7,10,0) else (if t.val < 20 then (10,7,7,10,1) else (10,7,7,10,2))) else (if t.val < 22 then (10,7,9,6,0) else (if t.val < 23 then (10,7,9,6,1) else (10,7,9,6,2))))))
def lookup5 : Table (Fin 24) := (.branch 49530 (.branch 40851 (.branch 35373 (.branch 35236 (.entry 35235 0) (.branch 35237 (.entry 35236 1) (.entry 35237 2))) (.branch 35374 (.entry 35373 3) (.branch 35375 (.entry 35374 4) (.entry 35375 5)))) (.branch 40989 (.branch 40852 (.entry 40851 6) (.branch 40853 (.entry 40852 7) (.entry 40853 8))) (.branch 40990 (.entry 40989 9) (.branch 40991 (.entry 40990 10) (.entry 40991 11))))) (.branch 55146 (.branch 49590 (.branch 49531 (.entry 49530 12) (.branch 49532 (.entry 49531 13) (.entry 49532 14))) (.branch 49591 (.entry 49590 15) (.branch 49592 (.entry 49591 16) (.entry 49592 17)))) (.branch 55206 (.branch 55147 (.entry 55146 18) (.branch 55148 (.entry 55147 19) (.entry 55148 20))) (.branch 55207 (.entry 55206 21) (.branch 55208 (.entry 55207 22) (.entry 55208 23))))))
lemma correct5 : Table.Correct (smallKey5 ∘ allowed5) lookup5 := by decide +kernel
def Test5 (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := (lookup5.lookup (smallKey5 (project5 q0 q1 q2 q3 q4 q5))).isSome = true
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Test5 q0 q1 q2 q3 q4 q5) := inferInstanceAs (Decidable (_ = true))
def goodCodes5 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(7,10,7,10,1),(7,10,7,10,2),(7,10,7,10,3),(7,10,11,8,1),(7,10,11,8,2),(7,10,11,8,3),(8,11,7,10,1),(8,11,7,10,2),(8,11,7,10,3),(8,11,11,8,1),(8,11,11,8,2),(8,11,11,8,3),(10,7,8,11,1),(10,7,8,11,2),(10,7,8,11,3),(10,7,10,7,1),(10,7,10,7,2),(10,7,10,7,3),(11,8,8,11,1),(11,8,8,11,2),(11,8,8,11,3),(11,8,10,7,1),(11,8,10,7,2),(11,8,10,7,3)}
def encode5 (q : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 5184 * ((q.1 - 1) % 12) + 432 * ((q.2.1 - 1) % 12) + 36 * ((q.2.2.1 - 1) % 12) + 3 * ((q.2.2.2.1 - 1) % 12) + 1 * ((q.2.2.2.2 - 1) % 3)
lemma forward5 : ∀ q ∈ goodCodes5, (lookup5.lookup (encode5 q)).isSome = true := by decide +kernel
def Compatible (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Prop := Test0 q0 q1 q2 q3 q4 q5 ∧ Test1 q0 q1 q2 q3 q4 q5 ∧ Test2 q0 q1 q2 q3 q4 q5 ∧ Test3 q0 q1 q2 q3 q4 q5 ∧ Test4 q0 q1 q2 q3 q4 q5 ∧ Test5 q0 q1 q2 q3 q4 q5
instance (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) : Decidable (Compatible q0 q1 q2 q3 q4 q5) := by unfold Compatible; infer_instance
lemma smallKey5_injective : Function.Injective smallKey5 := by
  rintro ⟨a,b,c,d,e⟩ ⟨f,g,h,i,j⟩ he
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have he' := e.isLt
  have hf := f.isLt
  have hg := g.isLt
  have hh := h.isLt
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [smallKey5] at he
  have h0 : a.val = f.val := by omega
  have h1 : b.val = g.val := by omega
  have h2 : c.val = h.val := by omega
  have h3 : d.val = i.val := by omega
  have h4 : e.val = j.val := by omega
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext h0,Fin.ext h1,Fin.ext h2,Fin.ext h3,Fin.ext h4⟩
lemma test5_exists (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) (h : Test5 q0 q1 q2 q3 q4 q5) :
    ∃ t : Fin 24, project5 q0 q1 q2 q3 q4 q5 = allowed5 t := by
  obtain ⟨t,_,ht⟩ := Table.exists_of_isSome (smallKey5 ∘ allowed5) lookup5 correct5
    (smallKey5 (project5 q0 q1 q2 q3 q4 q5)) h
  exact ⟨t,smallKey5_injective ht.symm⟩
def lift0 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift0_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift0 (projRow5_0 q) e = q := by decide +kernel
def lift1 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift1_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift1 (projRow5_1 q) e = q := by decide +kernel
def lift2 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift2_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift2 (projRow5_2 q) e = q := by decide +kernel
def lift3 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift3_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift3 (projRow5_3 q) e = q := by decide +kernel
def lift4 : Fin 3 → Fin 20 → Fin 60 := ![![0,1,2,3,4,5,12,13,16,18,19,22,46,47,48,49,51,53,54,59],![6,7,8,9,10,11,14,15,17,20,21,23,30,31,32,33,36,40,55,57],![24,25,26,27,28,29,34,35,37,38,39,41,42,43,44,45,50,52,56,58]]
lemma lift4_complete : ∀ q : Fin 60, ∃ e : Fin 20, lift4 (projRow5_4 q) e = q := by decide +kernel
def expanded (t : Fin 24) (e0 : Fin 5) (e1 : Fin 5) (e2 : Fin 5) (e3 : Fin 5) (e4 : Fin 20) (q5 : Fin 60) : Rows := rows (lift0 (allowed5 t).1 e0) (lift1 (allowed5 t).2.1 e1) (lift2 (allowed5 t).2.2.1 e2) (lift3 (allowed5 t).2.2.2.1 e3) (lift4 (allowed5 t).2.2.2.2 e4) q5
lemma factor (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) (h : Test5 q0 q1 q2 q3 q4 q5) :
    ∃ t : Fin 24, ∃ e0 : Fin 5, ∃ e1 : Fin 5, ∃ e2 : Fin 5, ∃ e3 : Fin 5, ∃ e4 : Fin 20,
      rows q0 q1 q2 q3 q4 q5 = expanded t e0 e1 e2 e3 e4 q5 := by
  obtain ⟨t,ht⟩ := test5_exists q0 q1 q2 q3 q4 q5 h
  have h0 := congrArg (fun z : SmallKeys5 => z.1) ht
  change projRow5_0 q0 = (allowed5 t).1 at h0
  obtain ⟨e0,he0⟩ := lift0_complete q0
  rw [h0] at he0
  have h1 := congrArg (fun z : SmallKeys5 => z.2.1) ht
  change projRow5_1 q1 = (allowed5 t).2.1 at h1
  obtain ⟨e1,he1⟩ := lift1_complete q1
  rw [h1] at he1
  have h2 := congrArg (fun z : SmallKeys5 => z.2.2.1) ht
  change projRow5_2 q2 = (allowed5 t).2.2.1 at h2
  obtain ⟨e2,he2⟩ := lift2_complete q2
  rw [h2] at he2
  have h3 := congrArg (fun z : SmallKeys5 => z.2.2.2.1) ht
  change projRow5_3 q3 = (allowed5 t).2.2.2.1 at h3
  obtain ⟨e3,he3⟩ := lift3_complete q3
  rw [h3] at he3
  have h4 := congrArg (fun z : SmallKeys5 => z.2.2.2.2) ht
  change projRow5_4 q4 = (allowed5 t).2.2.2.2 at h4
  obtain ⟨e4,he4⟩ := lift4_complete q4
  rw [h4] at he4
  refine ⟨t,e0,e1,e2,e3,e4,?_⟩
  unfold expanded
  rw [he0,he1,he2,he3,he4]
def CompleteAt (t : Fin 24) (e0 : Fin 5) : Prop :=
  ∀ e1 : Fin 5, ∀ e2 : Fin 5, ∀ e3 : Fin 5, ∀ q5 : Fin 60,
  Test4 (lift0 (allowed5 t).1 e0) (lift1 (allowed5 t).2.1 e1) (lift2 (allowed5 t).2.2.1 e2) (lift3 (allowed5 t).2.2.2.1 e3) 0 q5 →
  ∀ e4 : Fin 20,
  Test3 (lift0 (allowed5 t).1 e0) (lift1 (allowed5 t).2.1 e1) (lift2 (allowed5 t).2.2.1 e2) 0 (lift4 (allowed5 t).2.2.2.2 e4) q5 →
  Test2 (lift0 (allowed5 t).1 e0) (lift1 (allowed5 t).2.1 e1) 0 (lift3 (allowed5 t).2.2.2.1 e3) (lift4 (allowed5 t).2.2.2.2 e4) q5 →
  Test1 (lift0 (allowed5 t).1 e0) 0 (lift2 (allowed5 t).2.2.1 e2) (lift3 (allowed5 t).2.2.2.1 e3) (lift4 (allowed5 t).2.2.2.2 e4) q5 →
  Test0 0 (lift1 (allowed5 t).2.1 e1) (lift2 (allowed5 t).2.2.1 e2) (lift3 (allowed5 t).2.2.2.1 e3) (lift4 (allowed5 t).2.2.2.2 e4) q5 →
  (output.lookup (key (expanded t e0 e1 e2 e3 e4 q5))).isSome = true
instance (t : Fin 24) (e0 : Fin 5) : Decidable (CompleteAt t e0) := by unfold CompleteAt; infer_instance
lemma complete_of_factored (hc : ∀ t e0, CompleteAt t e0)
    (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60) (h : Compatible q0 q1 q2 q3 q4 q5) :
    (output.lookup (key (rows q0 q1 q2 q3 q4 q5))).isSome = true := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  obtain ⟨t,e0,e1,e2,e3,e4,he⟩ := factor q0 q1 q2 q3 q4 q5 h5
  have hq0 := congrFun he 0
  have hq1 := congrFun he 1
  have hq2 := congrFun he 2
  have hq3 := congrFun he 3
  have hq4 := congrFun he 4
  change q0 = (lift0 (allowed5 t).1 e0) at hq0
  change q1 = (lift1 (allowed5 t).2.1 e1) at hq1
  change q2 = (lift2 (allowed5 t).2.2.1 e2) at hq2
  change q3 = (lift3 (allowed5 t).2.2.2.1 e3) at hq3
  change q4 = (lift4 (allowed5 t).2.2.2.2 e4) at hq4
  dsimp only [Test0,project0] at h0
  rw [hq1,hq2,hq3,hq4] at h0
  dsimp only [Test1,project1] at h1
  rw [hq0,hq2,hq3,hq4] at h1
  dsimp only [Test2,project2] at h2
  rw [hq0,hq1,hq3,hq4] at h2
  dsimp only [Test3,project3] at h3
  rw [hq0,hq1,hq2,hq4] at h3
  dsimp only [Test4,project4] at h4
  rw [hq0,hq1,hq2,hq3] at h4
  rw [he]
  exact hc t e0 e1 e2 e3 q5 h4 e4 h3 h2 h1 h0

#print axioms factor
#print axioms complete_of_factored
end Erdos184Work.PureSixLocalFilter3
