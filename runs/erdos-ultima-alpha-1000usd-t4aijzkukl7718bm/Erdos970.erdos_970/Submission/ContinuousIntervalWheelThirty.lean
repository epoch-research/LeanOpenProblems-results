import Submission.ContinuousIntervalAffineSeed

/-! An exact period-30 affine seed, valid for all interval lengths and all
choices of residues for 2,3,5. Its use for arbitrary prime sets is justified by
the separate prefix-forcing theorem, not by replacing actual primes silently. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

private def smallModuli (i : ℕ) : ℕ := if i = 0 then 2 else if i = 1 then 3 else 5
private def smallResidues (a b c : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then a else if i = 1 then b else c

private theorem small_finite : ∀ (a : Fin 2) (b : Fin 3) (c : Fin 5) (n : Fin 31),
    4 * n.val ≤ 15 * count smallModuli (smallResidues a b c) 3 n.val + 24 ∧
    15 * count smallModuli (smallResidues a b c) 3 n.val ≤ 4 * n.val + 24 ∧
    (n.val = 30 → count smallModuli (smallResidues a b c) 3 n.val = 8) := by
  decide +kernel

private theorem small_normalized (r : ℕ → ℕ) (m : ℕ) :
    count smallModuli r 3 m =
      count smallModuli (smallResidues (r 0 % 2) (r 1 % 3) (r 2 % 5)) 3 m := by
  simp [count, Nat.forall_lt_succ_right, smallModuli, smallResidues, Nat.ModEq]

private theorem small_finite_bounds (r : ℕ → ℕ) (m : ℕ) (hm : m ≤ 30) :
    4 * m ≤ 15 * count smallModuli r 3 m + 24 ∧
    15 * count smallModuli r 3 m ≤ 4 * m + 24 ∧
    (m = 30 → count smallModuli r 3 m = 8) := by
  have hh := small_finite ⟨r 0 % 2, Nat.mod_lt _ (by omega)⟩
    ⟨r 1 % 3, Nat.mod_lt _ (by omega)⟩ ⟨r 2 % 5, Nat.mod_lt _ (by omega)⟩ ⟨m, by omega⟩
  simpa only [← small_normalized r m] using hh

private theorem small_period (r : ℕ → ℕ) (m : ℕ) :
    count smallModuli r 3 (m + 30) = count smallModuli r 3 m + 8 := by
  let f : ℕ → Prop := fun x => ∀ j < 3, ¬x ≡ r j [MOD smallModuli j]
  have hshift : (fun x => f (30 + x)) = f := by
    funext x
    simp [f, Nat.forall_lt_succ_right, smallModuli, Nat.ModEq, Nat.add_mod]
  have h30 : Nat.count f 30 = 8 := by
    simpa only [f, Nat.count_eq_card_filter_range, count] using
      (small_finite_bounds r 30 le_rfl).2.2 rfl
  simp only [count, ← Nat.count_eq_card_filter_range]
  change Nat.count f (m + 30) = Nat.count f m + 8
  rw [Nat.add_comm m 30, Nat.count_add]
  simp only [hshift, h30]
  omega

private theorem small_all_bounds (r : ℕ → ℕ) (m : ℕ) :
    4 * m ≤ 15 * count smallModuli r 3 m + 24 ∧
    15 * count smallModuli r 3 m ≤ 4 * m + 24 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 30
    · have hh := small_finite_bounds r m hm
      exact ⟨hh.1, hh.2.1⟩
    · have hi := ih (m - 30) (by omega)
      have hp := small_period r (m - 30)
      have he : m - 30 + 30 = m := by omega
      rw [he] at hp
      rw [hp]
      constructor <;> omega

/-- Density 4/15 and absolute discrepancy 8/5 give a regular seed. -/
theorem wheelThirty_regular :
    Regular (4 / 15) (affineLower (4 / 15) (8 / 5)) (affineUpper (4 / 15) (8 / 5)) :=
  affineSeed_regular _ _ (by norm_num) (by norm_num) (by norm_num)

/-- The period computation extends to every length before transfer is invoked. -/
theorem wheelThirty_bounds :
    IntervalBounds (affineLower (4 / 15) (8 / 5)) (affineUpper (4 / 15) (8 / 5))
      1 (Nat.nth Nat.Prime) 3 := by
  have hs : IntervalBounds (affineLower (4 / 15) (8 / 5)) (affineUpper (4 / 15) (8 / 5))
      1 smallModuli 3 := by
    intro m r
    have hn := small_all_bounds r m
    have hl : (4 : ℝ) * m ≤ 15 * count smallModuli r 3 m + 24 := by exact_mod_cast hn.1
    have hu : (15 : ℝ) * count smallModuli r 3 m ≤ 4 * m + 24 := by exact_mod_cast hn.2
    have hnon : (0 : ℝ) ≤ count smallModuli r 3 m := Nat.cast_nonneg _
    have hcard : count smallModuli r 3 m ≤ m := by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    have hcardR : (count smallModuli r 3 m : ℝ) ≤ m := by exact_mod_cast hcard
    simp only [affineLower, affineUpper, one_mul]
    exact ⟨max_le hnon (by linarith), le_min hcardR (by linarith)⟩
  apply hs.congr_prefix
  intro i hi
  have hfinite : ∀ i : Fin 3, (smallModuli i).Prime ∧
      Nat.count Nat.Prime (smallModuli i) = i.val := by decide +kernel
  have hh := Nat.nth_count (hfinite ⟨i, hi⟩).1
  rw [(hfinite ⟨i, hi⟩).2] at hh
  exact hh

/-- An explicitly positive run from this seed is a UNIFORM bound for arbitrary
k-prime sets. The three seed primes may first have to be adjoined. -/
theorem isJacobsthalBound_of_wheelThirty (k m : ℕ) (cells : ℕ → List ℕ)
    (hpos : 0 < (seedRun (fun i => (referenceMarginal i : ℝ)) cells 3
      (affineLower (4 / 15) (8 / 5)) (affineUpper (4 / 15) (8 / 5)) k).1 m) :
    IsJacobsthalBound k m :=
  isJacobsthalBound_of_seedRun 3 k m cells wheelThirty_regular wheelThirty_bounds hpos

#print axioms wheelThirty_bounds
#print axioms isJacobsthalBound_of_wheelThirty
end Erdos970.ContinuousInterval
