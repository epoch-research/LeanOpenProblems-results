import Submission.CyclicRowActions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Pure row-word model for six-color pattern 0. No coverage is asserted here. -/
namespace Erdos184Work.PureSixRowModel0
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
def length : Fin 6 → ℕ := ![5,5,5,5,5,5]
def choices : Fin 6 → ℕ := ![12,12,12,12,12,12]
lemma length_pos : ∀ i, 0 < length i := by decide +kernel
lemma choices_pos : ∀ i, 0 < choices i := by decide +kernel
instance (i : Fin 6) : NeZero (length i) := ⟨Nat.ne_of_gt (length_pos i)⟩
abbrev Rows := CyclicRowActions.Rows choices
abbrev E := Fin 30
abbrev W := Fin 72
def words0 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def markers0 : Fin 5 → W := ![2,4,6,8,10]
def word0 (q : Fin 12) (j : Fin 5) : W := markers0 (words0 q j)
def words1 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def markers1 : Fin 5 → W := ![2,16,18,20,22]
def word1 (q : Fin 12) (j : Fin 5) : W := markers1 (words1 q j)
def words2 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def markers2 : Fin 5 → W := ![4,16,30,32,34]
def word2 (q : Fin 12) (j : Fin 5) : W := markers2 (words2 q j)
def words3 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def markers3 : Fin 5 → W := ![6,18,30,44,46]
def word3 (q : Fin 12) (j : Fin 5) : W := markers3 (words3 q j)
def words4 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def markers4 : Fin 5 → W := ![8,20,32,44,58]
def word4 (q : Fin 12) (j : Fin 5) : W := markers4 (words4 q j)
def words5 : Fin 12 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,4,1,3],![0,3,1,2,4],![0,3,2,1,4]]
def markers5 : Fin 5 → W := ![10,22,34,46,58]
def word5 (q : Fin 12) (j : Fin 5) : W := markers5 (words5 q j)
def word : ∀ i, Fin (choices i) → Fin (length i) → W :=
  Fin.cases (word0) (Fin.cases (word1) (Fin.cases (word2) (Fin.cases (word3) (Fin.cases (word4) (Fin.cases (word5) ((fun i => Fin.elim0 i)))))))
def edge : E ≃ CyclicRowActions.Edges length := (finSigmaFinEquiv (n := length)).symm

def src (q : Rows) (e : E) : W := CyclicRowActions.source length choices word q (edge e)
def dst (q : Rows) (e : E) : W := CyclicRowActions.target length choices word q (edge e)
def rows (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Rows :=
  Fin.cases (q0) (Fin.cases (q1) (Fin.cases (q2) (Fin.cases (q3) (Fin.cases (q4) (Fin.cases (q5) ((fun i => Fin.elim0 i)))))))
def key (q : Rows) : ℕ := 248832 * (q 0).val + 20736 * (q 1).val + 1728 * (q 2).val + 144 * (q 3).val + 12 * (q 4).val + 1 * (q 5).val
def digit0 (j : ℕ) : Fin 12 := ⟨j / 248832 % 12,Nat.mod_lt _ (by decide)⟩
def digit1 (j : ℕ) : Fin 12 := ⟨j / 20736 % 12,Nat.mod_lt _ (by decide)⟩
def digit2 (j : ℕ) : Fin 12 := ⟨j / 1728 % 12,Nat.mod_lt _ (by decide)⟩
def digit3 (j : ℕ) : Fin 12 := ⟨j / 144 % 12,Nat.mod_lt _ (by decide)⟩
def digit4 (j : ℕ) : Fin 12 := ⟨j / 12 % 12,Nat.mod_lt _ (by decide)⟩
def digit5 (j : ℕ) : Fin 12 := ⟨j / 1 % 12,Nat.mod_lt _ (by decide)⟩
def unkey (j : ℕ) : Rows := rows (digit0 j) (digit1 j) (digit2 j) (digit3 j) (digit4 j) (digit5 j)
lemma key_lt (q : Rows) : key q < 2985984 := by
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  unfold key
  omega
lemma digit_key0 (q : Rows) : digit0 (key q) = q 0 := by
  apply Fin.ext
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  dsimp only [digit0,key]
  omega
lemma digit_key1 (q : Rows) : digit1 (key q) = q 1 := by
  apply Fin.ext
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  dsimp only [digit1,key]
  omega
lemma digit_key2 (q : Rows) : digit2 (key q) = q 2 := by
  apply Fin.ext
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  dsimp only [digit2,key]
  omega
lemma digit_key3 (q : Rows) : digit3 (key q) = q 3 := by
  apply Fin.ext
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  dsimp only [digit3,key]
  omega
lemma digit_key4 (q : Rows) : digit4 (key q) = q 4 := by
  apply Fin.ext
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  dsimp only [digit4,key]
  omega
lemma digit_key5 (q : Rows) : digit5 (key q) = q 5 := by
  apply Fin.ext
  have h0 : (q 0).val < 12 := (q 0).isLt
  have h1 : (q 1).val < 12 := (q 1).isLt
  have h2 : (q 2).val < 12 := (q 2).isLt
  have h3 : (q 3).val < 12 := (q 3).isLt
  have h4 : (q 4).val < 12 := (q 4).isLt
  have h5 : (q 5).val < 12 := (q 5).isLt
  dsimp only [digit5,key]
  omega
lemma unkey_key (q : Rows) : unkey (key q) = q := by
  funext i
  fin_cases i
  · exact digit_key0 q
  · exact digit_key1 q
  · exact digit_key2 q
  · exact digit_key3 q
  · exact digit_key4 q
  · exact digit_key5 q
lemma key_unkey {j : ℕ} (hj : j < 2985984) : key (unkey j) = j := by
  change 248832 * (j / 248832 % 12) + 20736 * (j / 20736 % 12) + 1728 * (j / 1728 % 12) + 144 * (j / 144 % 12) + 12 * (j / 12 % 12) + 1 * (j / 1 % 12) = j
  omega
lemma key_injective : Function.Injective key := by
  intro p q h
  rw [← unkey_key p,← unkey_key q,h]

#print axioms key_injective
end Erdos184Work.PureSixRowModel0
