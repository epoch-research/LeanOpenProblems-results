import FormalConjecturesUtil

/-!
Finite floor cells and a quantitative measure criterion.
No estimate for the measure of the prime-pair exceptional set is assumed to be proved here.
-/

namespace Erdos972Cells

lemma rational_interval_width {a b c d N : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hbN : b ≤ N) (hdN : d ≤ N)
    (h : (a : ℝ) / b < (c : ℝ) / d) :
    1 / (N : ℝ) ^ 2 ≤ (c : ℝ) / d - (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcross := (div_lt_div_iff₀ hbR hdR).mp h
  have hnat : a * d < c * b := by exact_mod_cast hcross
  have hgap : (a : ℝ) * d + 1 ≤ (c : ℝ) * b := by
    exact_mod_cast Nat.succ_le_of_lt hnat
  have hprod : (0 : ℝ) < (b : ℝ) * d := mul_pos hbR hdR
  have hprodN : (b : ℝ) * d ≤ (N : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul (Nat.cast_le.mpr hbN)
      (Nat.cast_le.mpr hdN) (Nat.cast_nonneg d) (Nat.cast_nonneg N)
  apply (one_div_le_one_div_of_le hprod hprodN).trans
  apply (div_le_iff₀ hprod).mpr
  have he : ((c : ℝ) / d - (a : ℝ) / b) * ((b : ℝ) * d) =
      (c : ℝ) * b - (a : ℝ) * d := by
    field_simp
  rw [he]
  linarith

/-- The floor pattern up to `N` is constant on a cell around an irrational slope.
Rational endpoints of the containing interval must also have denominator at most `N`. -/
theorem exists_floor_cell_in_rational_interval {α : ℝ} (hI : Irrational α)
    {a b c d N : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbN : b ≤ N) (hdN : d ≤ N)
    (hlo : (a : ℝ) / b < α) (hhi : α < (c : ℝ) / d) :
    ∃ u v : ℝ, (a : ℝ) / b ≤ u ∧ u < α ∧ α < v ∧ v ≤ (c : ℝ) / d ∧
      1 / (N : ℝ) ^ 2 ≤ v - u ∧
      ∀ x ∈ Set.Ioo u v, ∀ p : ℕ, 1 ≤ p → p ≤ N → ⌊x * p⌋₊ = ⌊α * p⌋₊ := by
  classical
  let s : Finset ℕ := Finset.Icc 1 N
  let f : ℕ × ℕ → ℝ := fun z => (z.1 : ℝ) / z.2
  let lower : Finset (ℕ × ℕ) := insert (a, b) (s.image fun p : ℕ => (⌊α * p⌋₊, p))
  let upper : Finset (ℕ × ℕ) := insert (c, d) (s.image fun p : ℕ => (⌊α * p⌋₊ + 1, p))
  have hα : 0 ≤ α := (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)).trans hlo.le
  have hlower : ∀ z ∈ lower, 0 < z.2 ∧ z.2 ≤ N ∧ f z < α := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact ⟨hb, hbN, hlo⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      have hp' : 1 ≤ p ∧ p ≤ N := Finset.mem_Icc.mp hp
      have hp0 : 0 < p := by omega
      refine ⟨hp0, hp'.2, ?_⟩
      apply (div_lt_iff₀ (Nat.cast_pos.mpr hp0)).mpr
      exact lt_of_le_of_ne (Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p)))
        ((hI.mul_natCast (by omega)).ne_nat _).symm
  have hupper : ∀ z ∈ upper, 0 < z.2 ∧ z.2 ≤ N ∧ α < f z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact ⟨hd, hdN, hhi⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      have hp' : 1 ≤ p ∧ p ≤ N := Finset.mem_Icc.mp hp
      have hp0 : 0 < p := by omega
      refine ⟨hp0, hp'.2, ?_⟩
      apply (lt_div_iff₀ (Nat.cast_pos.mpr hp0)).mpr
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (α * p)
  obtain ⟨l, hl, hmax⟩ := lower.exists_max_image f (Finset.insert_nonempty _ _)
  obtain ⟨r, hr, hmin⟩ := upper.exists_min_image f (Finset.insert_nonempty _ _)
  obtain ⟨hl0, hlN, hlα⟩ := hlower l hl
  obtain ⟨hr0, hrN, hαr⟩ := hupper r hr
  have hal : (a : ℝ) / b ≤ f l := hmax (a, b) (Finset.mem_insert_self _ _)
  have hrc : f r ≤ (c : ℝ) / d := hmin (c, d) (Finset.mem_insert_self _ _)
  refine ⟨f l, f r, hal, hlα, hαr, hrc,
    rational_interval_width hl0 hr0 hlN hrN (hlα.trans hαr), ?_⟩
  intro x hx p hp1 hpN
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hps : p ∈ s := Finset.mem_Icc.mpr ⟨hp1, hpN⟩
  have hleft : (⌊α * p⌋₊ : ℝ) / p < x :=
    (hmax (⌊α * p⌋₊, p)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hps, rfl⟩))).trans_lt hx.1
  have hright : x < ((⌊α * p⌋₊ + 1 : ℕ) : ℝ) / p :=
    hx.2.trans_le (hmin (⌊α * p⌋₊ + 1, p)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hps, rfl⟩)))
  have hx0 : 0 ≤ x :=
    ((div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)).trans hal).trans hx.1.le
  apply (Nat.floor_eq_iff (mul_nonneg hx0 (Nat.cast_nonneg p))).mpr
  refine ⟨((div_lt_iff₀ hp0).mp hleft).le, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using (lt_div_iff₀ hp0).mp hright

/-- Slopes failing the prime-pair search on the finite input window `(L, N]`. -/
def badWindow (L N : ℕ) : Set ℝ :=
  {α | ∀ p : ℕ, L < p → p ≤ N → p.Prime → ¬ (⌊α * p⌋₊).Prime}

open MeasureTheory in
/-- An irrational failure gives a definite lower bound on the exceptional measure. -/
theorem badWindow_measure_lower_bound {α : ℝ} (hI : Irrational α)
    {a b c d L N : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbN : b ≤ N) (hdN : d ≤ N)
    (hlo : (a : ℝ) / b < α) (hhi : α < (c : ℝ) / d)
    (hbad : α ∈ badWindow L N) :
    ENNReal.ofReal (1 / (N : ℝ) ^ 2) ≤
      volume (badWindow L N ∩ Set.Ioo ((a : ℝ) / b) ((c : ℝ) / d)) := by
  obtain ⟨u, v, hau, _, _, hvc, hwidth, hcell⟩ :=
    exists_floor_cell_in_rational_interval hI hb hd hbN hdN hlo hhi
  apply (ENNReal.ofReal_le_ofReal hwidth).trans
  rw [← Real.volume_Ioo]
  apply measure_mono
  intro x hx
  refine ⟨?_, hau.trans_lt hx.1, hx.2.trans_le hvc⟩
  intro p hLp hpN hp houtput
  apply hbad p hLp hpN hp
  rwa [hcell x hx p (by have := hp.two_le; omega) hpN] at houtput

open MeasureTheory in
/-- A sufficiently small exceptional measure is a certificate for the finite search.
The measure inequality is a hypothesis, not an estimate supplied by this theorem. -/
theorem prime_pair_of_small_badWindow_measure {α : ℝ} (hI : Irrational α)
    {a b c d L N : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbN : b ≤ N) (hdN : d ≤ N)
    (hlo : (a : ℝ) / b < α) (hhi : α < (c : ℝ) / d)
    (hmeasure : volume (badWindow L N ∩ Set.Ioo ((a : ℝ) / b) ((c : ℝ) / d)) <
      ENNReal.ofReal (1 / (N : ℝ) ^ 2)) :
    ∃ p : ℕ, L < p ∧ p ≤ N ∧ p.Prime ∧ (⌊α * p⌋₊).Prime := by
  by_contra h
  have hbad : α ∈ badWindow L N := by
    intro p hLp hpN hp houtput
    exact h ⟨p, hLp, hpN, hp, houtput⟩
  exact (not_le_of_gt hmeasure)
    (badWindow_measure_lower_bound hI hb hd hbN hdN hlo hhi hbad)

/-- The elementary prime-free neighborhood to the right of an integer. -/
lemma integer_right_interval_subset_badWindow {A L N : ℕ}
    (hA : 2 ≤ A) (hN : 0 < N) :
    Set.Ioo (A : ℝ) ((A : ℝ) + 1 / N) ⊆ badWindow L N := by
  intro x hx p _ hpN hp
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsmall : (x - A) * p < 1 := by
    have hsmallN : (x - A) * N < 1 :=
      (lt_div_iff₀ hNR).mp (by linarith [hx.2])
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpN)
      (by linarith [hx.1])).trans_lt hsmallN
  have hx0 : 0 ≤ x := (Nat.cast_nonneg A).trans hx.1.le
  have hfloor : ⌊x * p⌋₊ = A * p := by
    apply (Nat.floor_eq_iff (mul_nonneg hx0 (Nat.cast_nonneg p))).mpr
    push_cast
    constructor
    · exact mul_le_mul_of_nonneg_right hx.1.le (Nat.cast_nonneg p)
    · nlinarith
  rw [hfloor]
  exact Nat.not_prime_mul (by omega) hp.ne_one

open MeasureTheory in
/-- A global small-measure estimate on an integer unit interval is impossible:
the known rational obstruction already contributes measure at least `1/N`. -/
theorem integer_interval_bad_measure_lower_bound {A L N : ℕ}
    (hA : 2 ≤ A) (hN : 0 < N) :
    ENNReal.ofReal (1 / (N : ℝ)) ≤
      volume (badWindow L N ∩ Set.Ioo (A : ℝ) ((A : ℝ) + 1)) := by
  have hsub : Set.Ioo (A : ℝ) ((A : ℝ) + 1 / N) ⊆
      badWindow L N ∩ Set.Ioo (A : ℝ) ((A : ℝ) + 1) := by
    intro x hx
    refine ⟨integer_right_interval_subset_badWindow hA hN hx, hx.1, ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hinv : (1 : ℝ) / N ≤ 1 :=
      (div_le_one (Nat.cast_pos.mpr hN)).mpr hN1
    exact hx.2.trans_le (by linarith)
  have hm := measure_mono (μ := volume) hsub
  simpa only [Real.volume_Ioo, add_sub_cancel_left] using hm

#print axioms exists_floor_cell_in_rational_interval
#print axioms badWindow_measure_lower_bound
#print axioms prime_pair_of_small_badWindow_measure
#print axioms integer_interval_bad_measure_lower_bound

end Erdos972Cells
