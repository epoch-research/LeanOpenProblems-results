import Submission.FourTerms

/-!
# An eight-offset even-power obstruction

The eight selected terms at offsets `0, 3, 5, 6, 9, 10, 12, 15` can be paired
into a positive four-term arithmetic progression. Euler's four-term theorem
therefore excludes every even power of their product. These offsets are not
consecutive; this is a supporting obstruction, not the Erdős 672 conjecture.
-/

namespace Erdos672.Progression

open scoped BigOperators

/-- The eight-term product associated with the span-fifteen pairing. -/
def eightOffsetProduct (n d : ℕ) : ℕ :=
  n * (n + 3 * d) * (n + 5 * d) * (n + 6 * d) *
    (n + 9 * d) * (n + 10 * d) * (n + 12 * d) * (n + 15 * d)

/-- Four pair-products of the selected progression terms form an AP. -/
theorem eightOffsetProduct_pairing (n d : ℕ) :
    let A := n * (n + 9 * d)
    let S := 4 * n * d + 30 * d ^ 2
    A * (A + S) * (A + 2 * S) * (A + 3 * S) = eightOffsetProduct n d := by
  dsimp [eightOffsetProduct]
  ring

/-- Euler's four-term exclusion applies to the four positive pair-products. -/
theorem eightOffsetProduct_ne_square (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) :
    eightOffsetProduct n d ≠ q ^ 2 := by
  intro hpower
  let A := n * (n + 9 * d)
  let S := 4 * n * d + 30 * d ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  apply four_term_product_ne_square A S q hA hS
  calc
    A * (A + S) * (A + 2 * S) * (A + 3 * S) = eightOffsetProduct n d :=
      eightOffsetProduct_pairing n d
    _ = q ^ 2 := hpower

/-- The same selected eight-term product is not any even power. -/
theorem eightOffsetProduct_ne_even_power (n d q l : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hl : 2 ∣ l) :
    eightOffsetProduct n d ≠ q ^ l := by
  intro hpower
  apply eightOffsetProduct_ne_square n d (q ^ (l / 2)) hn hd
  calc
    eightOffsetProduct n d = q ^ l := hpower
    _ = (q ^ (l / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel hl]

/-- The index set of the span-fifteen pairing. -/
def eightOffsets : Finset ℕ := {0, 3, 5, 6, 9, 10, 12, 15}

/-- Identification with the finite-set product of the selected terms. -/
theorem product_eightOffsets (n d : ℕ) :
    (∏ i ∈ eightOffsets, (n + i * d)) = eightOffsetProduct n d := by
  norm_num [eightOffsets, eightOffsetProduct, Finset.prod_insert]
  ring

/-- The finite-set form of the selected-offset even-power obstruction. -/
theorem product_eightOffsets_ne_even_power (n d q l : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hl : 2 ∣ l) :
    (∏ i ∈ eightOffsets, (n + i * d)) ≠ q ^ l := by
  rw [product_eightOffsets]
  exact eightOffsetProduct_ne_even_power n d q l hn hd hl

/-- Arbitrary translates of the same index pattern are also excluded. -/
theorem product_translated_eightOffsets_ne_even_power (n d a q l : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hl : 2 ∣ l) :
    (∏ i ∈ eightOffsets, (n + (a + i) * d)) ≠ q ^ l := by
  have hn' : 0 < n + a * d := by positivity
  simpa only [Nat.add_mul, Nat.add_assoc] using
    product_eightOffsets_ne_even_power (n + a * d) d q l hn' hd hl

end Erdos672.Progression
