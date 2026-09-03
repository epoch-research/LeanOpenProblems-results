import Submission.Exploration

/-!
# Exact floor windows from rational approximation

Auxiliary results only; these do not settle Erdős 972.
-/

namespace Explore972

/-- Floor agreement only needs the multiplied approximation error to be
less than the minimum nonzero residue spacing. Inputs divisible by the
reduced denominator are excluded. -/
theorem floor_eq_of_reduced_error_bound {α : ℝ} {a b n : ℕ}
    (hα : 0 ≤ α) (hc : a.Coprime b) (hb : 0 < b)
    (hn : 0 < n) (hnd : ¬ b ∣ n)
    (hgap : |α - (a : ℝ) / b| * n * b < 1) :
    ⌊α * n⌋₊ = a * n / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbd : ¬ b ∣ a * n := fun hd => hnd (hc.symm.dvd_of_dvd_mul_left hd)
  have hr0 : 0 < a * n % b := Nat.pos_of_ne_zero (by
    simpa only [Nat.dvd_iff_mod_eq_zero] using hbd)
  have hrb : a * n % b < b := Nat.mod_lt _ hb
  have hr0R : (1 : ℝ) ≤ ((a * n % b : ℕ) : ℝ) := by exact_mod_cast hr0
  have hrbR : ((a * n % b : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast hrb
  have heq : ((a * n % b : ℕ) : ℝ) + (b : ℝ) * (a * n / b : ℕ) =
      (a : ℝ) * n := by exact_mod_cast Nat.mod_add_div (a * n) b
  have herr : |(α - (a : ℝ) / b) * n * b| < 1 := by
    simpa only [abs_mul, abs_of_pos hnR, abs_of_pos hbR] using hgap
  have herr_eq : (α - (a : ℝ) / b) * n * b = α * n * b - (a : ℝ) * n := by
    field_simp
  rw [herr_eq] at herr
  obtain ⟨hlo, hhi⟩ := abs_lt.mp herr
  apply (Nat.floor_eq_iff (mul_nonneg hα hnR.le)).mpr
  constructor
  · apply (le_of_mul_le_mul_right (a := (b : ℝ)))
    · nlinarith
    · exact hbR
  · apply (lt_of_mul_lt_mul_right (a := (b : ℝ)))
    · nlinarith
    · exact hbR.le

/-- An approximation of a reduced rational of height `b` within `1 / b²`
agrees with it on floors at every positive integer input below `b`. -/
theorem floor_eq_of_reduced_approximation {α : ℝ} {a b n : ℕ}
    (hα : 0 ≤ α) (hc : a.Coprime b) (hb : 0 < b)
    (hn : 0 < n) (hnb : n < b)
    (happ : |α - (a : ℝ) / b| < 1 / (b : ℝ) ^ 2) :
    ⌊α * n⌋₊ = a * n / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnbR : (n : ℝ) < b := by exact_mod_cast hnb
  apply floor_eq_of_reduced_error_bound hα hc hb hn
    (fun hd => (not_le_of_gt hnb) (Nat.le_of_dvd hn hd))
  calc
    |α - (a : ℝ) / b| * n * b < (1 / (b : ℝ) ^ 2) * n * b :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right happ hnR) hbR
    _ = (n : ℝ) / b := by field_simp
    _ < 1 := (div_lt_one hbR).mpr hnbR

/-- With a better approximation, the exact window can extend beyond the
denominator. At prime inputs the only possible denominator multiple is `b`
itself, so excluding that one input suffices. -/
theorem prime_floor_eq_in_long_approximation_window {α : ℝ} {a b p P : ℕ}
    (hα : 0 ≤ α) (hc : a.Coprime b) (hb : 1 < b)
    (hp : p.Prime) (hpb : p ≠ b) (hpP : p < P)
    (happ : |α - (a : ℝ) / b| < 1 / ((b : ℝ) * P)) :
    ⌊α * p⌋₊ = a * p / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast (hp.pos.trans hpP)
  have hpPR : (p : ℝ) < P := by exact_mod_cast hpP
  have hnd : ¬ b ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · omega
    · exact hpb h.symm
  apply floor_eq_of_reduced_error_bound hα hc (by omega) hp.pos hnd
  calc
    |α - (a : ℝ) / b| * p * b < (1 / ((b : ℝ) * P)) * p * b :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right happ hpR) hbR
    _ = (p : ℝ) / P := by field_simp
    _ < 1 := (div_lt_one hPR).mpr hpPR

/-- Nonnegative rational numbers with bounded value and bounded denominator
form a finite set. -/
lemma finite_bounded_rationals (A : ℝ) (hA : 0 ≤ A) (K : ℕ) :
    {q : ℚ | 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ A ∧ q.den ≤ K}.Finite := by
  let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  have hinj : Function.Injective f := by
    intro q r h
    have hh : q.num = r.num ∧ q.den = r.den := Prod.mk.inj h
    rw [← Rat.num_div_den q, ← Rat.num_div_den r, hh.1, hh.2]
  apply Set.Finite.of_finite_image (f := f) _ hinj.injOn
  apply ((Set.finite_Icc (0 : ℤ) ⌊A * K⌋).prod (Set.finite_Icc 0 K)).subset
  rintro _ ⟨q, ⟨hq0, hqA, hqK⟩, rfl⟩
  have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hnum : (q.num : ℝ) = (q : ℝ) * q.den := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hden0]
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq0)
  have hnumA : (q.num : ℝ) ≤ A * K := by
    rw [hnum]
    exact mul_le_mul hqA (by exact_mod_cast hqK) (Nat.cast_nonneg _) hA
  exact ⟨⟨hnum0, Int.le_floor.mpr hnumA⟩, ⟨Nat.zero_le _, hqK⟩⟩

/-- Irrational slopes greater than one have reduced nonnegative rational
approximations with arbitrarily large denominator and error less than `1/b²`. -/
theorem exists_large_reduced_approximation {α : ℝ} (hα : 1 < α)
    (hi : Irrational α) (K : ℕ) :
    ∃ a b : ℕ, K < b ∧ a.Coprime b ∧
      |α - (a : ℝ) / b| < 1 / (b : ℝ) ^ 2 := by
  have hInf := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hi
  obtain ⟨q, hq, hqnot⟩ := hInf.exists_notMem_finite
    (finite_bounded_rationals (α + 1) (by linarith) K)
  change |α - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 at hq
  have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have hsq : (1 : ℝ) ≤ (q.den : ℝ) ^ 2 := by nlinarith
  have herr : |α - (q : ℝ)| < 1 := hq.trans_le (by simpa using one_div_le_one_div_of_le zero_lt_one hsq)
  have hqpos : (0 : ℝ) < q := by have := (abs_lt.mp herr).2; linarith
  have hqA : (q : ℝ) ≤ α + 1 := by have := (abs_lt.mp herr).1; linarith
  have hdK : K < q.den := by
    by_contra h
    exact hqnot ⟨hqpos.le, hqA, Nat.le_of_not_gt h⟩
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hqpos.le)
  have hnR : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    have hnZ : (q.num.natAbs : ℤ) = q.num := by
      rw [Int.natCast_natAbs, abs_of_nonneg hn]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hnZ
  refine ⟨q.num.natAbs, q.den, hdK, q.reduced, ?_⟩
  rwa [hnR, ← Rat.cast_def]

/-- The new approximation window makes the required simultaneous-primality
condition a finite statement about two natural numbers. It does not prove
that a suitable prime exists in this window. -/
theorem infinite_iff_reduced_prime_windows {α : ℝ} (hα : 1 < α)
    (hi : Irrational α) :
    (primeSet α).Infinite ↔ ∀ N : ℕ, ∃ a b p : ℕ,
      a.Coprime b ∧ |α - (a : ℝ) / b| < 1 / (b : ℝ) ^ 2 ∧
      N < p ∧ p < b ∧ p.Prime ∧ (a * p / b).Prime := by
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h.exists_gt N
    obtain ⟨a, b, hpb, hc, happ⟩ := exists_large_reduced_approximation hα hi p
    have hf := floor_eq_of_reduced_approximation (by linarith : 0 ≤ α) hc
      (by omega : 0 < b) hp.1.pos hpb happ
    exact ⟨a, b, p, hc, happ, hNp, hpb, hp.1, hf ▸ hp.2⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨a, b, p, hc, happ, hNp, hpb, hp, hq⟩ := h N
    have hf := floor_eq_of_reduced_approximation (by linarith : 0 ≤ α) hc
      (by omega : 0 < b) hp.pos hpb happ
    exact ⟨p, ⟨hp, hf.symm ▸ hq⟩, hNp⟩

#print axioms floor_eq_of_reduced_error_bound
#print axioms prime_floor_eq_in_long_approximation_window
#print axioms floor_eq_of_reduced_approximation
#print axioms exists_large_reduced_approximation
#print axioms infinite_iff_reduced_prime_windows

end Explore972
