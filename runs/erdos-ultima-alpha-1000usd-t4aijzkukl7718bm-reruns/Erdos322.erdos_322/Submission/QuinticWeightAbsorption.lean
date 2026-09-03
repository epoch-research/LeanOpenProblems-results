import FormalConjecturesUtil

/-! Termwise splitting of the four weights in the nonsquare-curvature quintic
identity cannot produce five unweighted summands. This is only an obstruction
to that conversion, not to arbitrary identities or representation counts. -/
namespace Erdos322Research.QuinticWeightAbsorption

open Finset
noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Eight times the weights of the known four-term weighted identity. -/
def weights : Fin 4 → ℚ := ![6, 1, 1, 8]

private theorem weights_ne_zero (i : Fin 4) : weights i ≠ 0 := by
  fin_cases i <;> norm_num [weights]

private theorem valuations :
    padicValRat 2 (6 : ℚ) = 1 ∧ padicValRat 2 (1 : ℚ) = 0 ∧
      padicValRat 2 (8 : ℚ) = 3 := by
  have h2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide)
  have h3 : padicValRat 2 (3 : ℚ) = 0 := by
    change padicValRat 2 (↑(3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬2 ∣ 3)]
    rfl
  refine ⟨?_, by simp, ?_⟩
  · rw [show (6 : ℚ) = 2 * 3 by norm_num,
      padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0), h2, h3]
    norm_num
  · rw [show (8 : ℚ) = 2 ^ 3 by norm_num,
      padicValRat.pow (by norm_num : (2 : ℚ) ≠ 0), h2]
    norm_num

private theorem fifth_valuation {L w x : ℚ} (hL : L ≠ 0) (hw : w ≠ 0)
    (hx : x ^ 5 = L * w) :
    5 * padicValRat 2 x = padicValRat 2 L + padicValRat 2 w := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp only [zero_pow (by decide : 5 ≠ 0)] at hx
    exact mul_ne_zero hL hw hx.symm
  have h := congrArg (padicValRat 2) hx
  simpa only [padicValRat.pow hx0, padicValRat.mul hL hw, Nat.cast_ofNat] using h

/-- At most one of the three distinct coefficient classes can be a single
rational fifth power, even after a common nonzero rescaling. -/
theorem incompatible_single_terms {L : ℚ} (hL : L ≠ 0) :
    (¬ ((∃ x : ℚ, x ^ 5 = L * 6) ∧ (∃ y : ℚ, y ^ 5 = L))) ∧
    (¬ ((∃ x : ℚ, x ^ 5 = L * 6) ∧ (∃ y : ℚ, y ^ 5 = L * 8))) ∧
    (¬ ((∃ x : ℚ, x ^ 5 = L) ∧ (∃ y : ℚ, y ^ 5 = L * 8))) := by
  obtain ⟨h6, h1, h8⟩ := valuations
  have hv (x w : ℚ) (hw : w ≠ 0) (hx : x ^ 5 = L * w) :=
    fifth_valuation hL hw hx
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hx' := hv x 6 (by norm_num) hx
    have hy' := hv y 1 (by norm_num) (by simpa using hy)
    rw [h6] at hx'
    rw [h1] at hy'
    omega
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hx' := hv x 6 (by norm_num) hx
    have hy' := hv y 8 (by norm_num) hy
    rw [h6] at hx'
    rw [h8] at hy'
    omega
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hx' := hv x 1 (by norm_num) (by simpa using hx)
    have hy' := hv y 8 (by norm_num) hy
    rw [h1] at hx'
    rw [h8] at hy'
    omega

/-- Replacing each weighted term by a sum of rational fifth powers of multiples
of that same form requires at least six terms in total. The common scale may
be any nonzero rational, and the splitting coefficients may have either sign. -/
theorem termwise_absorption_at_least_six (s : Fin 4 → ℕ)
    (a : (i : Fin 4) → Fin (s i) → ℚ) {L : ℚ} (hL : L ≠ 0)
    (hs : ∀ i, ∑ j, a i j ^ 5 = L * weights i) : 6 ≤ ∑ i, s i := by
  classical
  have hpos (i : Fin 4) : 1 ≤ s i := by
    by_contra h
    have hz : s i = 0 := by omega
    have he : (univ : Finset (Fin (s i))) = ∅ := by
      apply card_eq_zero.mp
      simpa using hz
    have hi := hs i
    rw [he, sum_empty] at hi
    exact mul_ne_zero hL (weights_ne_zero i) hi.symm
  have hone (i : Fin 4) (hi : s i = 1) : ∃ x : ℚ, x ^ 5 = L * weights i := by
    obtain ⟨j, hj⟩ := card_eq_one.mp (show (univ : Finset (Fin (s i))).card = 1 by simpa)
    refine ⟨a i j, ?_⟩
    simpa only [hj, sum_singleton] using hs i
  have h01 : ¬ (s 0 = 1 ∧ s 1 = 1) := by
    rintro ⟨h0, h1⟩
    apply (incompatible_single_terms hL).1
    simpa [weights] using And.intro (hone 0 h0) (hone 1 h1)
  have h03 : ¬ (s 0 = 1 ∧ s 3 = 1) := by
    rintro ⟨h0, h3⟩
    apply (incompatible_single_terms hL).2.1
    simpa [weights] using And.intro (hone 0 h0) (hone 3 h3)
  have h13 : ¬ (s 1 = 1 ∧ s 3 = 1) := by
    rintro ⟨h1, h3⟩
    apply (incompatible_single_terms hL).2.2
    simpa [weights] using And.intro (hone 1 h1) (hone 3 h3)
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have h3 := hpos 3
  rw [Fin.sum_univ_four]
  omega

/-- The four quadratic forms in the weighted identity. -/
def forms (t : ℚ) : Fin 4 → ℚ :=
  ![1 - 2 * t ^ 2, 1 - 2 * t ^ 2 + 2 * t, 1 - 2 * t ^ 2 - 2 * t, 2 * t ^ 2]

/-- Even if their weights are allowed to vary, these four forms admit only
the known constant-sum identity, up to common rescaling. -/
theorem weighted_identity_classification (w : Fin 4 → ℚ) (N : ℚ) :
    (∀ t : ℚ, ∑ i, w i * forms t i ^ 5 = N) ↔
      ∀ i, w i = (N / 8) * weights i := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hn1 := h (-1)
    have hh := h (1 / 2)
    norm_num [Fin.sum_univ_four, forms, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 hn1 hh
    intro i
    fin_cases i <;> norm_num [weights]
    · linarith
    · linarith
    · change w 2 = N / 8
      linarith
    · change w 3 = N
      linarith
  · intro h t
    simp only [h, Fin.sum_univ_four]
    norm_num only [weights, forms, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring

/-- A nonzero constant identity formed by splitting these four forms into
rational multiples must use at least six fifth-power summands. This does not
exclude identities made from other quadratic forms. -/
theorem split_identity_at_least_six (s : Fin 4 → ℕ)
    (a : (i : Fin 4) → Fin (s i) → ℚ) {N : ℚ} (hN : N ≠ 0)
    (h : ∀ t : ℚ, ∑ i, ∑ j, (a i j * forms t i) ^ 5 = N) :
    6 ≤ ∑ i, s i := by
  have hw : ∀ t : ℚ, ∑ i, (∑ j, a i j ^ 5) * forms t i ^ 5 = N := by
    intro t
    simpa only [mul_pow, sum_mul] using h t
  exact termwise_absorption_at_least_six s a
    (div_ne_zero hN (by norm_num)) ((weighted_identity_classification _ N).mp hw)

end
end Erdos322Research.QuinticWeightAbsorption
