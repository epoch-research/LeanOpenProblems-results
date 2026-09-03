import Submission.E30HeightBridge

/-! A finite positive control for the all-height criterion, not an infinite family. -/
namespace Erdos30Research

def finiteHeightA : Finset ℤ := {0, 1, 4, 10, 18}
def finiteHeightB (s : ℤ) : ℤ :=
  if s = 1 then 8 else if s = 2 then 11 else if s = 3 then 4 else
  if s = 4 then 16 else if s = 5 then 13 else if s = 6 then 5 else
  if s = 7 then 0 else if s = 8 then 18 else if s = 9 then 17 else
  if s = 10 then 18 else if s = 11 then 1 else if s = 12 then 15 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem finiteHeight_rows : EdgeRowsInjective (13 : ℤ) (@liftResidue 13 finiteHeightA)
    (liftHeight finiteHeightB) := by
  intro t ht htm
  interval_cases t <;> decide

def finiteHeightCertificate : AllHeightBox 4 18 where
  A := finiteHeightA
  b := finiteHeightB
  heavy_sidon := by decide
  heavy_card := by decide
  rows := finiteHeight_rows
  heavy_box := by
    intro a ha
    simp only [finiteHeightA, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> norm_num
  light_box := by
    intro s hs hsm
    norm_num at hsm
    interval_cases s <;> norm_num [finiteHeightB]

theorem finiteHeight_exists : ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 247 ∧
    IsSidon (B : Set ℕ) ∧ B.card = 17 := by
  simpa using finiteHeightCertificate.nat_set (by norm_num : 2 ≤ (4 : ℕ))

/-- A finite lower bound only; it has no implication for the asymptotic target. -/
theorem finiteHeight_card_bound : 17 ≤ h 247 := by
  obtain ⟨B, hBN, hB, hcard⟩ := finiteHeight_exists
  simpa only [hcard] using card_le_h hBN hB

/-- The row criterion does not impose modular Sidonicity at the old period.
These four marks occur in the finite positive control. -/
example : (52 : ZMod 273) + 234 = 0 + 13 := by decide
example : (52 : ℤ) + 234 ≠ 0 + 13 := by norm_num

#print axioms finiteHeight_rows
#print axioms finiteHeightCertificate
#print axioms finiteHeight_exists
#print axioms finiteHeight_card_bound
end Erdos30Research
