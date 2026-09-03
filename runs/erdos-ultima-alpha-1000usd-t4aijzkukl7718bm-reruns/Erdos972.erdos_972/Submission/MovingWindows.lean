import Submission.Exploration

/-!
# Prime-free moving windows near a noninteger rational slope

These results are auxiliary. The slope changes with the location of the window;
no single irrational slope with a prime-free tail is constructed.
-/

namespace Explore972

lemma prime_mod_six {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : p % 2 ≠ 0 := by
    intro h
    have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  have h3 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 3) hp).mp hd
    omega
  omega

/-- The shift interval `[1/3, 2/3)` gives a parity obstruction for slope `5/3`. -/
lemma five_thirds_shift_not_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {β : ℝ} (hβlo : 1 / 3 ≤ β) (hβhi : β < 2 / 3) :
    ¬ (⌊(5 / 3 : ℝ) * p + β⌋₊).Prime := by
  rcases prime_mod_six hp hp3 with hmod | hmod
  · have hpeq : p = 6 * (p / 6) + 1 := by omega
    have hpeqR : (p : ℝ) = 6 * (p / 6 : ℕ) + 1 := by exact_mod_cast hpeq
    have hk : 1 ≤ p / 6 := by omega
    have hf : ⌊(5 / 3 : ℝ) * p + β⌋₊ = 2 * (5 * (p / 6) + 1) := by
      apply (Nat.floor_eq_iff' (by omega : 2 * (5 * (p / 6) + 1) ≠ 0)).mpr
      push_cast
      constructor <;> linarith
    rw [hf]
    exact Nat.not_prime_mul (by omega) (by omega)
  · have hpeq : p = 6 * (p / 6) + 5 := by omega
    have hpeqR : (p : ℝ) = 6 * (p / 6 : ℕ) + 5 := by exact_mod_cast hpeq
    have hf : ⌊(5 / 3 : ℝ) * p + β⌋₊ = 2 * (5 * (p / 6) + 4) := by
      apply (Nat.floor_eq_iff' (by omega : 2 * (5 * (p / 6) + 4) ≠ 0)).mpr
      push_cast
      constructor <;> linarith
    rw [hf]
    exact Nat.not_prime_mul (by omega) (by omega)

/-- The corresponding homogeneous prime-free window. -/
theorem five_thirds_moving_window {α : ℝ} {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hlo : 1 / 3 ≤ (α - 5 / 3) * p)
    (hhi : (α - 5 / 3) * p < 2 / 3) :
    p ∉ primeSet α := by
  intro h
  have hn := five_thirds_shift_not_prime hp hp3 hlo hhi
  have he : (5 / 3 : ℝ) * p + (α - 5 / 3) * p = α * p := by ring
  rw [he] at hn
  exact hn h.2

/-- Even away from integer slopes, one can find irrational slopes with a
prime-free window from `N` through `3N/2`. This is not an eventual tail. -/
theorem exists_irrational_moving_gap (N : ℕ) (hN : 3 < N) :
    ∃ α : ℝ, 5 / 3 < α ∧ α < 5 / 3 + 1 / N ∧ Irrational α ∧
      ∀ p : ℕ, N ≤ p → 2 * p ≤ 3 * N → p ∉ primeSet α := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hinterval : (5 / 3 : ℝ) + 1 / (3 * N) < 5 / 3 + 4 / (9 * N) := by
    have hpos := one_div_pos.mpr hNr
    field_simp
    nlinarith
  obtain ⟨α, hi, hlo, hhi⟩ := exists_irrational_btwn hinterval
  have hαlo : (5 / 3 : ℝ) < α := by
    have := one_div_pos.mpr (show (0 : ℝ) < 3 * N by positivity)
    linarith
  have hαhi : α < (5 / 3 : ℝ) + 1 / N := by
    have hfrac : (4 : ℝ) / (9 * N) < 1 / N := by
      field_simp
      nlinarith
    linarith
  refine ⟨α, hαlo, hαhi, hi, ?_⟩
  intro p hNp hpN hp
  have hpr : (N : ℝ) ≤ p := by exact_mod_cast hNp
  have hpNr : (2 : ℝ) * p ≤ 3 * N := by exact_mod_cast hpN
  have hδpos : (0 : ℝ) < α - 5 / 3 := by linarith
  have hδlo : (1 : ℝ) < (α - 5 / 3) * (3 * N) :=
    (div_lt_iff₀ (show (0 : ℝ) < 3 * N by positivity)).mp (by linarith)
  have hδhi : (α - 5 / 3) * (9 * N) < (4 : ℝ) :=
    (lt_div_iff₀ (show (0 : ℝ) < 9 * N by positivity)).mp (by linarith)
  apply five_thirds_moving_window hp.1 (by omega) _ _ hp
  · have hmul := mul_le_mul_of_nonneg_left hpr hδpos.le
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left hpNr hδpos.le
    nlinarith


/-- For any fixed slope, the unshifted parity window covers only finitely
many indices. Thus this particular window cannot itself be a prime-free tail. -/
theorem five_thirds_window_finite (α : ℝ) :
    {p : ℕ | 1 / 3 ≤ (α - 5 / 3) * p ∧ (α - 5 / 3) * p < 2 / 3}.Finite := by
  by_cases hδ : 0 < α - 5 / 3
  · apply (Set.finite_Iic ⌊(2 / 3) / (α - 5 / 3)⌋₊).subset
    intro p hp
    apply Nat.le_floor
    apply (le_div_iff₀ hδ).mpr
    nlinarith [hp.2]
  · apply Set.finite_empty.subset
    intro p hp
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hδ)
      (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    have := hp.1
    norm_num at this ⊢
    linarith

#print axioms five_thirds_window_finite

#print axioms five_thirds_shift_not_prime
#print axioms five_thirds_moving_window
#print axioms exists_irrational_moving_gap


open Filter in
open scoped Topology in
/-- The moving-window construction can be arranged as a convergent sequence,
but its limit is the rational number `5/3`. -/
theorem exists_moving_gap_sequence :
    ∃ a : ℕ → ℝ,
      (∀ n, 5 / 3 < a n ∧ Irrational (a n)) ∧
      Tendsto a atTop (𝓝 (5 / 3)) ∧
      ∀ n p : ℕ, n + 4 ≤ p → 2 * p ≤ 3 * (n + 4) → p ∉ primeSet (a n) := by
  have hex := fun n : ℕ => exists_irrational_moving_gap (n + 4) (by omega)
  choose a hlo hhi hirr hgap using hex
  refine ⟨a, fun n => ⟨hlo n, hirr n⟩, ?_, hgap⟩
  have ht : Tendsto (fun n : ℕ => 1 / ((n + 4 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 4).mpr tendsto_one_div_atTop_nhds_zero_nat
  have hu : Tendsto (fun n : ℕ => (5 / 3 : ℝ) + 1 / ((n + 4 : ℕ) : ℝ))
      atTop (𝓝 (5 / 3)) := by
    simpa using ht.const_add (5 / 3)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (hlo n).le) (fun n => (hhi n).le)

#print axioms exists_moving_gap_sequence

end Explore972
