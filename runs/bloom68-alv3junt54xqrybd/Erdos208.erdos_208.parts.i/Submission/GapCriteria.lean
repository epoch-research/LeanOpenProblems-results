import Submission.SquarefreeRoth

/-!
# Short-interval criteria for the squarefree-gap assertion

These equivalences isolate the uniform number-theoretic assertion needed by
`Submission.Spec`.  They do not assume either theorem from that module.
-/

open Filter

namespace SquarefreeCriteria

local notation "s" => SquarefreeSqrt.s

lemma s_zero : s 0 = 1 := by
  apply le_antisymm
  · exact (Nat.isLeast_nth_of_infinite SquarefreeSqrt.infinite_squarefree 0).2
      ⟨squarefree_one, by simp⟩
  · exact SquarefreeSqrt.s_pos 0

/-- A uniform short-interval bound, including its positive implicit constant. -/
def IntervalBound (ε : ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    ∃ m : ℕ, Squarefree m ∧ x < m ∧
      (m : ℝ) - (x : ℝ) ≤ C * (x : ℝ) ^ ε

lemma gap_isBigO_iff_eventual_bound (ε : ℝ) :
    ((fun n => (s (n + 1) - s n : ℝ)) =O[atTop]
      (fun n => (s n : ℝ) ^ ε)) ↔
    ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      (s (n + 1) - s n : ℝ) ≤ C * (s n : ℝ) ^ ε := by
  have hbasic :
      ((fun n => (s (n + 1) - s n : ℝ)) =O[atTop]
        (fun n => (s n : ℝ) ^ ε)) ↔
      ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
        (s (n + 1) - s n : ℝ) ≤ C * (s n : ℝ) ^ ε := by
    simp only [Asymptotics.isBigO_iff, Filter.eventually_atTop,
      Real.norm_eq_abs, abs_of_pos (SquarefreeSqrt.gap_pos _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [hbasic]
  constructor
  · rintro ⟨C, N, h⟩
    have hpow : 0 < (s N : ℝ) ^ ε :=
      Real.rpow_pos_of_pos (by exact_mod_cast SquarefreeSqrt.s_pos N) ε
    have hmul : 0 < C * (s N : ℝ) ^ ε :=
      (SquarefreeSqrt.gap_pos N).trans_le (h N le_rfl)
    exact ⟨C, (mul_pos_iff_of_pos_right hpow).mp hmul, N, h⟩
  · rintro ⟨C, _, N, h⟩
    exact ⟨C, N, h⟩

/-- Every positive integer is bracketed by successive squarefree numbers. -/
lemma exists_bracketing (x : ℕ) (hx : 1 ≤ x) :
    ∃ n : ℕ, s n ≤ x ∧ x < s (n + 1) := by
  have hex : ∃ k : ℕ, x < s k := by
    refine ⟨x + 1, ?_⟩
    exact (Nat.lt_succ_self x).trans_le (SquarefreeSqrt.s_strictMono.id_le (x + 1))
  let k := Nat.find hex
  have hk : x < s k := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, s_zero] at hk
    omega
  have hprev : s (k - 1) ≤ x := by
    have h := Nat.find_min hex (show k - 1 < Nat.find hex by dsimp [k]; omega)
    exact le_of_not_gt h
  refine ⟨k - 1, hprev, ?_⟩
  have heq : k - 1 + 1 = k := by omega
  simpa only [heq] using hk

/-- For nonnegative exponents, bounds on enumerated gaps and all short intervals coincide. -/
theorem gap_isBigO_iff_intervalBound {ε : ℝ} (hε : 0 ≤ ε) :
    ((fun n => (s (n + 1) - s n : ℝ)) =O[atTop]
      (fun n => (s n : ℝ) ^ ε)) ↔ IntervalBound ε := by
  rw [gap_isBigO_iff_eventual_bound]
  constructor
  · rintro ⟨C, hC, N, h⟩
    refine ⟨C, hC, max 1 (s N), ?_⟩
    intro x hx
    obtain ⟨n, hnx, hxn⟩ := exists_bracketing x ((le_max_left _ _).trans hx)
    have hN : N ≤ n := by
      by_contra hN
      have hnN : n + 1 ≤ N := by omega
      have hsnN := SquarefreeSqrt.s_strictMono.monotone hnN
      have hsNx : s N ≤ x := (le_max_right _ _).trans hx
      omega
    refine ⟨s (n + 1), SquarefreeSqrt.s_squarefree _, hxn, ?_⟩
    have hnxreal : (s n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnx
    have hpow : (s n : ℝ) ^ ε ≤ (x : ℝ) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hnxreal hε
    have hbound := (h n hN).trans (mul_le_mul_of_nonneg_left hpow hC.le)
    linarith
  · rintro ⟨C, hC, N, h⟩
    refine ⟨C, hC, N, ?_⟩
    intro n hn
    have hsn : N ≤ s n := hn.trans (SquarefreeSqrt.s_strictMono.id_le n)
    obtain ⟨m, hmsf, hnm, hm⟩ := h (s n) hsn
    have hnext : (s (n + 1) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast SquarefreeSqrt.next_le_of_squarefree hmsf hnm
    linarith

/-- The unit-constant interval assertion conventionally used for the conjecture. -/
def UnitIntervals (ε : ℝ) : Prop :=
  ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    ∃ m : ℕ, Squarefree m ∧ x < m ∧
      (m : ℝ) - (x : ℝ) ≤ (x : ℝ) ^ ε

/-- An implicit constant can be absorbed into any strictly larger exponent. -/
lemma unitIntervals_of_intervalBound_lt {δ ε : ℝ} (hδε : δ < ε)
    (h : IntervalBound δ) : UnitIntervals ε := by
  obtain ⟨C, _, N, h⟩ := h
  have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε - δ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hδε)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hlim.eventually (eventually_ge_atTop C))
  refine ⟨max 1 (max N M), ?_⟩
  intro x hx
  have hxN : N ≤ x := (le_max_left N M).trans ((le_max_right _ _).trans hx)
  have hxM : M ≤ x := (le_max_right N M).trans ((le_max_right _ _).trans hx)
  have hxpos : 0 < (x : ℝ) := by
    exact_mod_cast (show 0 < x from (by omega))
  obtain ⟨m, hmsf, hxm, hm⟩ := h x hxN
  refine ⟨m, hmsf, hxm, hm.trans ?_⟩
  calc
    C * (x : ℝ) ^ δ ≤ (x : ℝ) ^ (ε - δ) * (x : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_right (hM x hxM) (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) ^ ε := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring

lemma unitIntervals_of_intervalBound_half {ε : ℝ} (hε : 0 < ε)
    (h : IntervalBound (ε / 2)) : UnitIntervals ε :=
  unitIntervals_of_intervalBound_lt (by linarith) h

/-- Exact equivalence with the customary all-positive-exponents interval conjecture. -/
theorem all_exponents_iff_unitIntervals :
    (∀ ε > (0 : ℝ), (fun n => (s (n + 1) - s n : ℝ)) =O[atTop]
      (fun n => (s n : ℝ) ^ ε)) ↔
    (∀ ε > (0 : ℝ), UnitIntervals ε) := by
  constructor
  · intro h ε hε
    exact unitIntervals_of_intervalBound_half hε
      ((gap_isBigO_iff_intervalBound (by linarith : 0 ≤ ε / 2)).mp
        (h (ε / 2) (by linarith)))
  · intro h ε hε
    apply (gap_isBigO_iff_intervalBound hε.le).mpr
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨1, zero_lt_one, N, by simpa only [one_mul] using hN⟩

#print axioms gap_isBigO_iff_intervalBound
#print axioms all_exponents_iff_unitIntervals

/-- The elementary argument establishes unit-length constants above exponent `1/3`. -/
theorem unitIntervals_of_third_lt {ε : ℝ} (hε : (1 / 3 : ℝ) < ε) :
    UnitIntervals ε := by
  let δ : ℝ := (ε + 1 / 3) / 2
  have hδ : (1 / 3 : ℝ) ≤ δ := by dsimp [δ]; linarith
  apply unitIntervals_of_intervalBound_lt (δ := δ) (by dsimp [δ]; linarith)
  apply (gap_isBigO_iff_intervalBound (by linarith : 0 ≤ δ)).mp
  exact SquarefreeCubic.squarefree_gap_isBigO hδ

/-- Roth's bound yields unit constants for every exponent strictly above `1/4`. -/
theorem unitIntervals_of_quarter_lt {ε : ℝ} (hε : (1 / 4 : ℝ) < ε) :
    UnitIntervals ε := by
  let δ : ℝ := (ε + 1 / 4) / 2
  have hδ : (1 / 4 : ℝ) ≤ δ := by dsimp [δ]; linarith
  apply unitIntervals_of_intervalBound_lt (δ := δ) (by dsimp [δ]; linarith)
  apply (gap_isBigO_iff_intervalBound (by linarith : 0 ≤ δ)).mp
  exact SquarefreeRoth.squarefree_gap_isBigO hδ

#print axioms unitIntervals_of_quarter_lt

end SquarefreeCriteria
