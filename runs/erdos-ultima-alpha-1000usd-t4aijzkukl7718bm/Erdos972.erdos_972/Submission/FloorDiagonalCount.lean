import Submission.RationalRotationCount

/-! Bounds for multiplicative diagonals in a floor strip. These are not
bounds for the signed off-diagonal correlation in Erdős 972. -/
namespace Erdos972FloorDiagonalCount

open Finset Erdos972RationalRotationCount
set_option maxHeartbeats 1000000

/-- A sufficiently good reduced rational approximation bounds every common
factor occurring in a multiplicative diagonal. The factor need not be prime. -/
lemma diagonal_factor_le {α : ℝ} {a q N m k p : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α - (a : ℝ) / q| * N ≤ 1)
    (hN : N ≤ q ^ 2) (hm : 0 < m) (hmp : m * p ≤ N)
    (hf : k * p = ⌊α * (m * p : ℕ)⌋₊) : p ≤ 2 * q := by
  by_contra hp
  have hpq : 2 * q < p := by omega
  have hp0 : 0 < p := by omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp0
  have hpqR : 2 * (q : ℝ) < p := by exact_mod_cast hpq
  have hmpR : (m : ℝ) * p ≤ N := by exact_mod_cast hmp
  have herr₀ : |α - (a : ℝ) / q| * ((m : ℝ) * p) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmpR (abs_nonneg _)).trans happrox
  have herr : |α * q * m * p - (a : ℝ) * m * p| ≤ q := by
    have he : α * q * m * p - (a : ℝ) * m * p =
        (q : ℝ) * (α - (a : ℝ) / q) * ((m : ℝ) * p) := by
      field_simp
    rw [he, abs_mul, abs_mul, abs_of_nonneg hqR.le,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ m * p)]
    nlinarith only [mul_le_mul_of_nonneg_left herr₀ hqR.le]
  have hlo := Nat.floor_le (show 0 ≤ α * (m * p : ℕ) by positivity)
  have hhi := Nat.lt_floor_add_one (α * (m * p : ℕ))
  rw [← hf] at hlo hhi
  push_cast at hlo hhi
  have hloq := mul_le_mul_of_nonneg_right hlo hqR.le
  have hhiq := mul_lt_mul_of_pos_right hhi hqR
  have hleft : (a : ℝ) * m < k * q + 1 := by
    apply (mul_lt_mul_iff_left₀ hpR).mp
    nlinarith only [hhiq, (abs_le.mp herr).1, hpqR]
  have hright : (k : ℝ) * q < a * m + 1 := by
    apply (mul_lt_mul_iff_left₀ hpR).mp
    nlinarith only [hloq, (abs_le.mp herr).2, hpqR, hqR]
  have hleft' : a * m < k * q + 1 := by exact_mod_cast hleft
  have hright' : k * q < a * m + 1 := by exact_mod_cast hright
  have he : a * m = k * q := by omega
  have hqm : q ∣ m := haq.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q k)
  have hqm' : q ≤ m := Nat.le_of_dvd hm hqm
  have hmul : q * p ≤ N := (Nat.mul_le_mul_right p hqm').trans hmp
  have hqq : q * p ≤ q * q := by simpa [pow_two] using hmul.trans hN
  have hpq' : p ≤ q := by
    have hh : (q : ℝ) * p ≤ (q : ℝ) * q := by exact_mod_cast hqq
    exact_mod_cast (mul_le_mul_iff_right₀ hqR).mp hh
  omega

noncomputable def diagonalRows (α : ℝ) (N p : ℕ) : Finset ℕ :=
  (Ioc 0 (N / p)).filter fun m => Int.fract (α * m) < 1 / (p : ℝ)

lemma row_card_le_rotation (α : ℝ) (N p : ℕ) :
    (diagonalRows α N p).card ≤ (rotationInterval α (N / p + 1) 0 (1 / (p : ℝ))).card := by
  apply card_le_card
  intro m hm
  obtain ⟨hmI, hmfrac⟩ := mem_filter.mp hm
  obtain ⟨hm0, hmN⟩ := mem_Ioc.mp hmI
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), Int.fract_nonneg _, hmfrac⟩

lemma row_empty_of_lt {α : ℝ} {N p : ℕ} (hNp : N < p) :
    diagonalRows α N p = ∅ := by
  simp [diagonalRows, Nat.div_eq_of_lt hNp]

/-- An explicit row bound that retains the short interval width 1/p;
in particular, its rational-denominator error is not O(p*q). -/
lemma diagonal_row_bound {α : ℝ} {a q N p : ℕ}
    (hq : 0 < q) (haq : a.Coprime q) (hp : 0 < p)
    (happrox : |α - (a : ℝ) / q| * N ≤ 1) :
    ((diagonalRows α N p).card : ℝ) ≤
      10 * N / (p : ℝ)^2 + (2 * N / (q : ℝ) + 5 * q) / p + 1 := by
  by_cases hNp : N < p
  · rw [row_empty_of_lt hNp, card_empty, Nat.cast_zero]
    positivity
  have hpN : p ≤ N := by omega
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let K := N / p + 1
  let E := |α - (a : ℝ) / q| * (K : ℝ)
  have hK : (K : ℝ) ≤ 2 * N / p := by
    have hdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have hpNR : (p : ℝ) ≤ N := Nat.cast_le.mpr hpN
    dsimp [K]
    push_cast
    apply (le_div_iff₀ hpR).mpr
    have hd := (le_div_iff₀ hpR).mp hdiv
    nlinarith only [hd, hpNR]
  have hE : E ≤ 2 / (p : ℝ) := by
    dsimp [E]
    calc
      _ ≤ |α - (a : ℝ) / q| * (2 * N / p) :=
        mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      _ = 2 * (|α - (a : ℝ) / q| * N) / p := by ring
      _ ≤ 2 * 1 / p := by gcongr
      _ = _ := by ring
  have hcount := rotationInterval_card_le hq haq
    (show (0 : ℝ) ≤ 1 / p by positivity) (show 0 ≤ E by dsimp [E]; positivity)
    (le_refl E)
  have hfirst : ((K / q : ℕ) : ℝ) + 1 ≤ 2 * N / ((p : ℝ) * q) + 1 := by
    have hd : ((K / q : ℕ) : ℝ) ≤ (K : ℝ) / q := Nat.cast_div_le
    have hkk := div_le_div_of_nonneg_right hK hqR.le
    have he : (2 * (N : ℝ) / p) / q = 2 * N / ((p : ℝ) * q) := by ring
    rw [he] at hkk
    linarith
  have hsecond : (q : ℝ) * (1 / p - 0 + 2 * E) + 1 ≤ 5 * q / p + 1 := by
    simp only [sub_zero]
    calc
      _ ≤ (q : ℝ) * (1 / p + 2 * (2 / p)) + 1 := by gcongr
      _ = _ := by ring
  have hbound := (Nat.cast_le.mpr (row_card_le_rotation α N p) :
    ((diagonalRows α N p).card : ℝ) ≤ (rotationInterval α K 0 (1 / (p : ℝ))).card)
  apply (hbound.trans hcount).trans
  calc
    _ ≤ (2 * N / ((p : ℝ) * q) + 1) * (5 * q / p + 1) :=
      mul_le_mul hfirst hsecond (by simp only [sub_zero]; dsimp [E]; positivity) (by positivity)
    _ = _ := by field_simp; ring

/-- A fractional-part row produces exactly the multiplicative diagonal,
with the other multiplier equal to floor(alpha*m). -/
lemma floor_diagonal_of_fract {α : ℝ} {m p : ℕ}
    (hα : 0 ≤ α) (hp : 0 < p)
    (hf : Int.fract (α * m) < 1 / (p : ℝ)) :
    ⌊α * m⌋₊ * p = ⌊α * (m * p : ℕ)⌋₊ := by
  have hx : 0 ≤ α * m := mul_nonneg hα (Nat.cast_nonneg m)
  have hfr : Int.fract (α * m) = α * m - (⌊α * m⌋₊ : ℝ) := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor hx]
    rfl
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hf' := (lt_div_iff₀ hpR).mp hf
  rw [hfr] at hf'
  symm
  apply (Nat.floor_eq_iff (show 0 ≤ α * (m * p : ℕ) by positivity)).mpr
  push_cast
  constructor
  · have hh := mul_le_mul_of_nonneg_right (Nat.floor_le hx) hpR.le
    nlinarith only [hh]
  · nlinarith only [hf']

/-- Exact classification of an equal-factor floor relation. -/
lemma floor_diagonal_iff {α : ℝ} {m k p : ℕ}
    (hα : 0 ≤ α) (hp : 0 < p) :
    k * p = ⌊α * (m * p : ℕ)⌋₊ ↔
      k = ⌊α * m⌋₊ ∧ Int.fract (α * m) < 1 / (p : ℝ) := by
  constructor
  · intro hf
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hx : 0 ≤ α * m := by positivity
    have hlo := Nat.floor_le (show 0 ≤ α * (m * p : ℕ) by positivity)
    have hhi := Nat.lt_floor_add_one (α * (m * p : ℕ))
    rw [← hf] at hlo hhi
    push_cast at hlo hhi
    have hlow : (k : ℝ) ≤ α * m := by
      apply (mul_le_mul_iff_left₀ hpR).mp
      nlinarith only [hlo]
    have hhigh : α * m < (k : ℝ) + 1 := by
      apply (mul_lt_mul_iff_left₀ hpR).mp
      nlinarith only [hhi, hp1]
    have hk : k = ⌊α * m⌋₊ := ((Nat.floor_eq_iff hx).mpr ⟨hlow, hhigh⟩).symm
    refine ⟨hk, ?_⟩
    have hfr : Int.fract (α * m) = α * m - (k : ℝ) := by
      rw [Int.fract, ← Int.natCast_floor_eq_floor hx, ← hk]
      rfl
    rw [hfr]
    apply (lt_div_iff₀ hpR).mpr
    nlinarith only [hhi]
  · rintro ⟨rfl, hf⟩
    exact floor_diagonal_of_fract hα hp hf

lemma diagonal_row_empty_of_large {α : ℝ} {a q N p : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α - (a : ℝ) / q| * N ≤ 1)
    (hN : N ≤ q ^ 2) (hp : 2 * q < p) :
    diagonalRows α N p = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro m hm
  obtain ⟨hmI, hmfrac⟩ := mem_filter.mp hm
  obtain ⟨hm0, hmN⟩ := mem_Ioc.mp hmI
  have hp0 : 0 < p := by omega
  have hmp : m * p ≤ N :=
    (Nat.mul_le_mul_right p hmN).trans (Nat.div_mul_le_self N p)
  have hf := floor_diagonal_of_fract hα hp0 hmfrac
  have hb := diagonal_factor_le hα hq haq happrox hN hm0 hmp hf
  omega

lemma harmonic_interval_upper (V Q : ℕ) :
    (∑ p ∈ Ioc V Q, 1 / (p : ℝ)) ≤ 1 + Real.log Q := by
  have hsub : Ioc V Q ⊆ Icc 1 Q := by
    intro p hp
    obtain ⟨hpV, hpQ⟩ := mem_Ioc.mp hp
    exact mem_Icc.mpr ⟨by omega, hpQ⟩
  calc
    _ ≤ ∑ p ∈ Icc 1 Q, (p : ℝ)⁻¹ := by
      simpa only [one_div] using
        (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p)) :
          (∑ p ∈ Ioc V Q, (p : ℝ)⁻¹) ≤ ∑ p ∈ Icc 1 Q, (p : ℝ)⁻¹)
    _ = (harmonic Q : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log Q

/-- The count of all multiplicative diagonal rows above V, with no prime
restriction. This keeps a decaying N/V term and only a logarithmic loss on
the denominator error. -/
theorem diagonal_count_bound {α : ℝ} {a q N V : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α - (a : ℝ) / q| * N ≤ 1)
    (hN : N ≤ q ^ 2) (hV : 0 < V) :
    (∑ p ∈ Ioc V N, ((diagonalRows α N p).card : ℝ)) ≤
      10 * N / (V : ℝ) + (2 * N / (q : ℝ) + 5 * q) *
        (1 + Real.log (2 * q : ℕ)) + 2 * q := by
  classical
  let S := (Ioc V N).filter fun p => p ≤ 2 * q
  have he : (∑ p ∈ Ioc V N, ((diagonalRows α N p).card : ℝ)) =
      ∑ p ∈ S, ((diagonalRows α N p).card : ℝ) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro p hp hpS
    have hpq : 2 * q < p := by
      have hn : ¬ p ≤ 2 * q := by
        intro hh
        exact hpS (mem_filter.mpr ⟨hp, hh⟩)
      omega
    rw [diagonal_row_empty_of_large hα hq haq happrox hN hpq, card_empty, Nat.cast_zero]
  have hsub : S ⊆ Ioc V (2 * q) := by
    intro p hp
    obtain ⟨hpI, hpq⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, hpq⟩
  have hreduce : (∑ p ∈ Ioc V N, ((diagonalRows α N p).card : ℝ)) ≤
      ∑ p ∈ Ioc V (2 * q), ((diagonalRows α N p).card : ℝ) := by
    rw [he]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Nat.cast_nonneg _)
  have hL : 0 ≤ 1 + Real.log (2 * q : ℕ) := by
    linarith [Real.log_natCast_nonneg (2 * q)]
  by_cases hVq : V ≤ 2 * q
  · have hsq : (∑ p ∈ Ioc V (2 * q), 1 / (p : ℝ)^2) ≤ 1 / (V : ℝ) := by
      have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) hV.ne' hVq
      simp only [one_div]
      exact hh.trans (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _)))
    have hharm := harmonic_interval_upper V (2 * q)
    have hcard : ((Ioc V (2 * q)).card : ℝ) ≤ 2 * q := by
      rw [Nat.card_Ioc]
      exact_mod_cast Nat.sub_le (2 * q) V
    have hC : 0 ≤ 2 * (N : ℝ) / q + 5 * q := by positivity
    calc
      _ ≤ ∑ p ∈ Ioc V (2 * q), ((diagonalRows α N p).card : ℝ) := hreduce
      _ ≤ ∑ p ∈ Ioc V (2 * q),
          (10 * N / (p : ℝ)^2 + (2 * N / (q : ℝ) + 5 * q) / p + 1) := by
        apply sum_le_sum
        intro p hp
        exact diagonal_row_bound hq haq (by have := (mem_Ioc.mp hp).1; omega) happrox
      _ = 10 * N * (∑ p ∈ Ioc V (2 * q), 1 / (p : ℝ)^2) +
          (2 * N / (q : ℝ) + 5 * q) * (∑ p ∈ Ioc V (2 * q), 1 / (p : ℝ)) +
          (Ioc V (2 * q)).card := by
        simp only [sum_add_distrib, mul_sum, mul_one_div, sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 10 * N * (1 / (V : ℝ)) +
          (2 * N / (q : ℝ) + 5 * q) * (1 + Real.log (2 * q : ℕ)) + 2 * q :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity))
          (mul_le_mul_of_nonneg_left hharm hC)) hcard
      _ = _ := by ring
  · have hzero : Ioc V (2 * q) = ∅ := Ioc_eq_empty_of_le (by omega)
    rw [hzero, sum_empty] at hreduce
    exact hreduce.trans (by positivity)

/-- The unsigned count also bounds arbitrary real weights whose absolute
values are bounded on the actual rows. No cancellation is assumed. -/
theorem weighted_diagonal_bound {α : ℝ} {a q N V : ℕ}
    (hα : 0 ≤ α) (hq : 0 < q) (haq : a.Coprime q)
    (happrox : |α - (a : ℝ) / q| * N ≤ 1)
    (hN : N ≤ q ^ 2) (hV : 0 < V) (w : ℕ → ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ p ∈ Ioc V N, ∀ m ∈ diagonalRows α N p, |w p m| ≤ B) :
    |∑ p ∈ Ioc V N, ∑ m ∈ diagonalRows α N p, w p m| ≤
      B * (10 * N / (V : ℝ) + (2 * N / (q : ℝ) + 5 * q) *
        (1 + Real.log (2 * q : ℕ)) + 2 * q) := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ Ioc V N, ((diagonalRows α N p).card : ℝ) * B := by
      apply sum_le_sum
      intro p hp
      apply (abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ m ∈ diagonalRows α N p, B := sum_le_sum (hw p hp)
        _ = _ := by simp
    _ = B * (∑ p ∈ Ioc V N, ((diagonalRows α N p).card : ℝ)) := by
      rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (diagonal_count_bound hα hq haq happrox hN hV) hB

#print axioms diagonal_factor_le
#print axioms diagonal_row_bound
#print axioms diagonal_count_bound

end Erdos972FloorDiagonalCount
