import Submission.LambertRowSubtractedBoundary
import Submission.MovingLambertTailBarrier

/-!
The factorial-cleared, uniformly bounded image count cannot overlap the
available unfiltered height detector. This does not exclude other clearings
or other constructions and does not settle Spec.lean.
-/
namespace RowSubtractedCountingBarrier

open Finset Erdos68Development LambertDifferenceOperators LambertRawBounds
  LambertTailRows LambertUnfilteredDetection LambertRowSubtractedBoundary

lemma tail_ge_row (d e n : ℕ) (hd : 2 ≤ d) (hde : d ≤ e) :
    geometricRowTail e n ≤ tail d n := by
  rw [tail_eq_shifted_rows d n hd]
  have hs : Summable (fun k => row n (k+(d-2))) :=
    (summable_nat_add_iff (d-2)).mpr (summable_row n)
  have hh := hs.le_tsum (e-d) (fun k _ => row_nonneg _ _)
  simpa only [row, show e-d+(d-2)+2=e by omega] using hh

lemma half_row_lower (n : ℕ) (hn : 18 ≤ n) :
    1/((n/2+1).factorial : ℝ)^2 ≤ geometricRowTail (n/2+1) n := by
  let e := n/2+1
  have he : 2 ≤ e := by dsimp [e]; omega
  have hquot : n/e ≤ 1 := by
    have hh : n/e < 2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < e)).mpr (by dsimp [e]; omega)
    omega
  have hf : (2 : ℝ) ≤ e.factorial := by exact_mod_cast Nat.factorial_le he
  have hp : (e.factorial : ℝ)^(n/e) ≤ e.factorial := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ e.factorial) hquot
  have hfd : (0 : ℝ) < (e.factorial : ℝ)-1 := by linarith
  change 1/(e.factorial : ℝ)^2 ≤ 1/((e.factorial : ℝ)^(n/e)*((e.factorial : ℝ)-1))
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ e.factorial) (n/e)]

/-- The direct row-subtracted tail, not a comparison series, has a quadratic
factorial-scaled lower bound in the detector's starting-index range. -/
theorem scaled_tail_ge_square (d H : ℕ) (hd : 2 ≤ d) (hH : 18 ≤ H)
    (hcut : d ≤ H/2+1) : (H : ℝ)^2 ≤ (H.factorial : ℝ)*tail d H := by
  have hfac : (H : ℝ)^2*((H/2+1).factorial : ℝ)^2 ≤ H.factorial := by
    exact_mod_cast half_index_factorial_square_bound H hH
  have hh : (H : ℝ)^2 ≤ (H.factorial : ℝ)/((H/2+1).factorial : ℝ)^2 :=
    (le_div_iff₀ (by positivity)).mpr hfac
  calc
    _ ≤ (H.factorial : ℝ)/((H/2+1).factorial : ℝ)^2 := hh
    _ = (H.factorial : ℝ)*(1/((H/2+1).factorial : ℝ)^2) := by ring
    _ ≤ (H.factorial : ℝ)*tail d H :=
      mul_le_mul_of_nonneg_left ((half_row_lower H hH).trans (tail_ge_row d _ H hd hcut)) (by positivity)

lemma factorial_growth (H D T : ℕ) (hT : H+D ≤ T) :
    H.factorial*H^D ≤ T.factorial := by
  have hp : H^D ≤ (H+1).ascFactorial D :=
    (Nat.pow_le_pow_left (by omega : H ≤ H+1) D).trans (Nat.pow_succ_le_ascFactorial (H+1) D)
  calc
    _ ≤ H.factorial*(H+1).ascFactorial D := Nat.mul_le_mul_left _ hp
    _ = (H+D).factorial := Nat.factorial_mul_ascFactorial H D
    _ ≤ T.factorial := Nat.factorial_le hT

lemma cleared_bound_ge_power (d H D T : ℕ) (hd : 2 ≤ d) (hH : 18 ≤ H)
    (hcut : d ≤ H/2+1) (hT : H+D ≤ T) (η : ℝ) (hη : tail d H ≤ η) :
    (H : ℝ)^D ≤ (T.factorial : ℝ)*η := by
  have hs := scaled_tail_ge_square d H hd hH hcut
  have hHone : (1 : ℝ) ≤ (H : ℝ)^2 := by
    have : (18 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  have hpos : 0 ≤ tail d H := by
    have hh : 0 < (H.factorial : ℝ)*tail d H := lt_of_lt_of_le (by linarith) hs
    exact ((mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < H.factorial)).mp hh).le
  have hfac : (H.factorial : ℝ)*(H : ℝ)^D ≤ T.factorial := by exact_mod_cast factorial_growth H D T hT
  calc
    _ ≤ (H : ℝ)^D*((H.factorial : ℝ)*tail d H) :=
      le_mul_of_one_le_right (by positivity) (hHone.trans hs)
    _ = ((H.factorial : ℝ)*(H : ℝ)^D)*tail d H := by ring
    _ ≤ (T.factorial : ℝ)*tail d H := mul_le_mul_of_nonneg_right hfac hpos
    _ ≤ _ := mul_le_mul_of_nonneg_left hη (by positivity)

/-- A stronger obstruction using only the first image's floor range.
Any common box that contains that image already has too many possible output
codes for the desired pigeonhole inequality at this weight budget. -/
theorem floor_range_cardinality_not_lt (d H D Q T M L : ℕ)
    (hd : 12 ≤ d) (hH : 420*d ≤ H) (hT : H+D ≤ T) (hL : 1 ≤ L)
    (hheight : Q+1 ≤ H^d)
    (hM : (T.factorial : ℝ)*tail d H < (M+1 : ℕ)) :
    ¬ L*(M+1)^d < (Q+1)^D := by
  have hpow := cleared_bound_ge_power d H D T (by omega) (by omega)
    (by omega) hT (tail d H) le_rfl
  have hMp : H^D ≤ M+1 := by exact_mod_cast (hpow.trans_lt hM).le
  have hfull : (Q+1)^D ≤ L*(M+1)^d := by
    calc
      _ ≤ (H^d)^D := Nat.pow_le_pow_left hheight D
      _ = (H^D)^d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (M+1)^d := Nat.pow_le_pow_left hMp d
      _ ≤ L*(M+1)^d := Nat.le_mul_of_pos_left _ (by omega)
  exact not_lt_of_ge hfull

/-- Even with the shared denominator charged only once, the counting
hypothesis is impossible with T! clearing, a uniform row bound, and the
available d!-scale coefficient budget. No rationality assumption is used. -/
theorem cardinality_not_lt (d H D Q T M L : ℕ)
    (hd : 12 ≤ d) (hH : 420*d ≤ H) (hD : 1 ≤ D) (hQ : 1 ≤ Q)
    (hheight : 4*Q ≤ d.factorial) (hT : H+D ≤ T) (hL : 1 ≤ L)
    (η : ℝ) (hη : tail d H ≤ η)
    (hM : (D : ℝ)*Q*((T.factorial : ℝ)*η) ≤ M) :
    ¬ L*(M+1)^d < (Q+1)^D := by
  have hpow := cleared_bound_ge_power d H D T (by omega) (by omega) (by omega) hT η hη
  have hnonneg : 0 ≤ (T.factorial : ℝ)*η := (by positivity : (0 : ℝ) ≤ (H : ℝ)^D).trans hpow
  have hDQ : (1 : ℝ) ≤ (D : ℝ)*Q := by exact_mod_cast (show 1 ≤ D*Q by nlinarith)
  have hMp : H^D ≤ M := by
    have hh : (H : ℝ)^D ≤ M := hpow.trans ((le_mul_of_one_le_left hnonneg hDQ).trans hM)
    exact_mod_cast hh
  have hfac : d.factorial ≤ H^d := by
    calc
      _ ≤ d^d := Nat.factorial_le_pow d
      _ ≤ H^d := Nat.pow_le_pow_left (by omega) d
  have hq : Q+1 ≤ H^d := (show Q+1 ≤ d.factorial by omega).trans hfac
  have hfull : (Q+1)^D ≤ L*(M+1)^d := by
    calc
      _ ≤ (H^d)^D := Nat.pow_le_pow_left hq D
      _ = (H^D)^d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (M+1)^d := Nat.pow_le_pow_left (by omega) d
      _ ≤ L*(M+1)^d := Nat.le_mul_of_pos_left _ (by omega)
  exact not_lt_of_ge hfull

#print axioms scaled_tail_ge_square
#print axioms floor_range_cardinality_not_lt
#print axioms cardinality_not_lt

end RowSubtractedCountingBarrier
