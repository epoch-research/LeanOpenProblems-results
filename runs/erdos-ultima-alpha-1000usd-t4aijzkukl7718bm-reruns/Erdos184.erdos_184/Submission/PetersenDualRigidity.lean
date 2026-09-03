import FormalConjecturesUtil

/-! Exact real linear algebra for the twenty nine-cycle edge patterns of
Petersen. The serial graph-family interpretation is documented externally;
this file proves only the displayed algebraic implications. It is not a
proof or disproof of Erdős 184. -/
namespace Erdos184.PetersenDualRigidity
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- The twenty explicit nine-edge pattern equations. -/
def Tight (x : Fin 15 → ℝ) : Prop :=
  (x 1 + x 2 + x 3 + x 4 + x 6 + x 7 + x 8 + x 10 + x 12 = 1) ∧
  (x 0 + x 1 + x 4 + x 5 + x 6 + x 7 + x 10 + x 11 + x 12 = 1) ∧
  (x 0 + x 2 + x 4 + x 5 + x 6 + x 7 + x 9 + x 10 + x 13 = 1) ∧
  (x 1 + x 2 + x 3 + x 4 + x 5 + x 8 + x 9 + x 11 + x 13 = 1) ∧
  (x 3 + x 4 + x 6 + x 7 + x 8 + x 9 + x 10 + x 11 + x 13 = 1) ∧
  (x 1 + x 2 + x 5 + x 6 + x 8 + x 9 + x 10 + x 12 + x 13 = 1) ∧
  (x 0 + x 2 + x 3 + x 5 + x 7 + x 9 + x 11 + x 12 + x 13 = 1) ∧
  (x 0 + x 1 + x 3 + x 6 + x 9 + x 10 + x 11 + x 12 + x 13 = 1) ∧
  (x 0 + x 2 + x 3 + x 6 + x 7 + x 8 + x 9 + x 11 + x 14 = 1) ∧
  (x 0 + x 1 + x 3 + x 5 + x 8 + x 9 + x 10 + x 11 + x 14 = 1) ∧
  (x 0 + x 1 + x 4 + x 5 + x 6 + x 8 + x 9 + x 12 + x 14 = 1) ∧
  (x 0 + x 2 + x 4 + x 7 + x 8 + x 9 + x 10 + x 12 + x 14 = 1) ∧
  (x 1 + x 2 + x 3 + x 4 + x 6 + x 9 + x 11 + x 12 + x 14 = 1) ∧
  (x 3 + x 4 + x 5 + x 7 + x 9 + x 10 + x 11 + x 12 + x 14 = 1) ∧
  (x 1 + x 2 + x 3 + x 4 + x 5 + x 7 + x 10 + x 13 + x 14 = 1) ∧
  (x 0 + x 2 + x 4 + x 5 + x 6 + x 8 + x 11 + x 13 + x 14 = 1) ∧
  (x 0 + x 1 + x 4 + x 7 + x 8 + x 10 + x 11 + x 13 + x 14 = 1) ∧
  (x 0 + x 1 + x 3 + x 6 + x 7 + x 8 + x 12 + x 13 + x 14 = 1) ∧
  (x 0 + x 2 + x 3 + x 5 + x 8 + x 10 + x 12 + x 13 + x 14 = 1) ∧
  (x 1 + x 2 + x 5 + x 6 + x 7 + x 11 + x 12 + x 13 + x 14 = 1)

/-- The twenty equations uniquely determine each branch weight. -/
theorem rigidity {x : Fin 15 → ℝ} (h : Tight x) : ∀ j, x j = 1 / 9 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  intro j
  fin_cases j
  · change x 0 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (-7 / 18 : ℝ) * h4 + (-7 / 18 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (4 / 9 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (-1 / 3 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 1 = (1 / 9 : ℝ)
    linear_combination (-1 / 3 : ℝ) * h0 + (4 / 9 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (2 / 3 : ℝ) * h3 + (-7 / 18 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-5 / 9 : ℝ) * h6 + (4 / 9 : ℝ) * h7 + (11 / 18 : ℝ) * h8 + (-1 / 2 : ℝ) * h9 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (-1 / 3 : ℝ) * h12 + (7 / 18 : ℝ) * h14 + (-7 / 18 : ℝ) * h15
  · change x 2 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (-7 / 18 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (-7 / 18 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 3 = (1 / 9 : ℝ)
    linear_combination (2 / 3 : ℝ) * h0 + (-5 / 9 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (-1 / 3 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (-7 / 18 : ℝ) * h5 + (4 / 9 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (-7 / 18 : ℝ) * h8 + (1 / 2 : ℝ) * h9 + (1 / 9 : ℝ) * h10 + (-7 / 18 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 4 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (-7 / 18 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (-7 / 18 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 5 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (-1 / 3 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (4 / 9 : ℝ) * h6 + (-5 / 9 : ℝ) * h7 + (-7 / 18 : ℝ) * h8 + (1 / 2 : ℝ) * h9 + (1 / 9 : ℝ) * h10 + (-7 / 18 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 6 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (-1 / 3 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (-7 / 18 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 7 = (1 / 9 : ℝ)
    linear_combination (-1 / 3 : ℝ) * h0 + (4 / 9 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (11 / 18 : ℝ) * h8 + (-1 / 2 : ℝ) * h9 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (-1 / 3 : ℝ) * h12 + (7 / 18 : ℝ) * h14 + (-7 / 18 : ℝ) * h15
  · change x 8 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (-1 / 3 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 9 = (1 / 9 : ℝ)
    linear_combination (-1 / 3 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (-7 / 18 : ℝ) * h15
  · change x 10 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (2 / 9 : ℝ) * h2 + (-1 / 3 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (-7 / 18 : ℝ) * h8 + (1 / 2 : ℝ) * h9 + (-7 / 18 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 11 = (1 / 9 : ℝ)
    linear_combination (-1 / 3 : ℝ) * h0 + (4 / 9 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (-7 / 18 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 12 = (1 / 9 : ℝ)
    linear_combination (1 / 6 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (-1 / 3 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (4 / 9 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (-7 / 18 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (-1 / 9 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 13 = (1 / 9 : ℝ)
    linear_combination (-1 / 3 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (1 / 6 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (4 / 9 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (-1 / 2 : ℝ) * h9 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (-1 / 3 : ℝ) * h12 + (7 / 18 : ℝ) * h14 + (1 / 9 : ℝ) * h15
  · change x 14 = (1 / 9 : ℝ)
    linear_combination (-1 / 3 : ℝ) * h0 + (-1 / 18 : ℝ) * h1 + (-5 / 18 : ℝ) * h2 + (-1 / 3 : ℝ) * h3 + (1 / 9 : ℝ) * h4 + (1 / 9 : ℝ) * h5 + (-1 / 18 : ℝ) * h6 + (-1 / 18 : ℝ) * h7 + (1 / 9 : ℝ) * h8 + (1 / 9 : ℝ) * h10 + (1 / 9 : ℝ) * h11 + (1 / 6 : ℝ) * h12 + (7 / 18 : ℝ) * h14 + (1 / 9 : ℝ) * h15

/-- One rooted nine-cycle with its root edge removed. -/
def longPathWeight (x : Fin 15 → ℝ) : ℝ :=
  x 1 + x 4 + x 5 + x 6 + x 7 + x 10 + x 11 + x 12

/-- The two local tight families and one tight global column force the
closing edge and the distinguished short-cycle weight. The hypotheses are
explicit equations; no graph interpretation is asserted by this theorem. -/
theorem serial_rigidity {t : ℕ} (d b : Fin t → Fin 15 → ℝ) (z : ℝ)
    (hb : ∀ i, Tight (b i))
    (hd : ∀ i, Tight (fun j => if j = 0 then b i 0 else d i j))
    (hz : z + ∑ i, longPathWeight (d i) = 1) :
    (∀ i j, b i j = 1 / 9) ∧
    (∀ i j, j ≠ 0 → d i j = 1 / 9) ∧
    z = 1 - 8 * (t : ℝ) / 9 ∧
    z + ∑ i, b i 0 = 1 - 7 * (t : ℝ) / 9 := by
  have hb' : ∀ i j, b i j = 1 / 9 := fun i => rigidity (hb i)
  have hd' : ∀ i j, j ≠ 0 → d i j = 1 / 9 := by
    intro i j hj
    simpa only [if_neg hj] using rigidity (hd i) j
  have hpath : ∀ i, longPathWeight (d i) = 8 / 9 := by
    intro i
    simp only [longPathWeight]
    rw [hd' i 1 (by decide), hd' i 4 (by decide), hd' i 5 (by decide),
      hd' i 6 (by decide), hd' i 7 (by decide), hd' i 10 (by decide),
      hd' i 11 (by decide), hd' i 12 (by decide)]
    norm_num
  have hs : (∑ i, longPathWeight (d i)) = 8 * (t : ℝ) / 9 := by
    simp only [hpath, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hs' : (∑ i, b i 0) = (t : ℝ) / 9 := by
    simp [hb', div_eq_mul_inv]
  rw [hs] at hz
  refine ⟨hb', hd', ?_, ?_⟩
  · linarith
  · rw [hs']
    linarith

end Erdos184.PetersenDualRigidity
