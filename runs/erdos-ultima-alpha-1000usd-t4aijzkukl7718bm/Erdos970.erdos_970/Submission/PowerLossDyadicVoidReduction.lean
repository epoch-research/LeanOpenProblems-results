import Submission.LongDyadicVoidReduction

/-! A weaker, still explicitly CONDITIONAL, dyadic route to the quadratic
Jacobsthal conjecture. A fixed sublinear power of the prime budget may be lost
at every doubling step. No doubling estimate is proved in this file. -/
namespace Erdos970.GapAverages
open Finset Real Filter

/-- This is an UNPROVED hypothesis. The loss is allowed to grow as a fixed
power of the number of selected primes, rather than being an absolute constant. -/
def PowerLossDyadicVoidBound (A α : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, P.card ≤ m →
    coveredFraction P (2*m) ≤
      (A*((P.card : ℝ)+2)^α) * coveredFraction P m ^ 2

/-- The second moment already provides a useful base probability after
multiplication by any fixed sublinear power of the prime budget. -/
lemma eventually_power_scaled_void_base (A α : ℝ) (hA : 0 < A) (hα : α < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      (A*((k : ℝ)+2)^α) * coveredFraction P k ≤
        exp (-((1-α)/2 * log ((k : ℝ)+2))) := by
  let d := exp (-WeightedMertens.reciprocalConstant-1)
  let η := (1-α)/2
  have hd : 0 < d := exp_pos _
  have hη : 0 < η := by dsimp [η]; linarith
  have ht : Tendsto (fun k : ℕ => (k : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith : ∀ k : ℕ, (k : ℝ) ≤ (k : ℝ)+2)
      tendsto_natCast_atTop_atTop
  have he := ht.eventually ((isLittleO_log_rpow_atTop hη).def
    (show 0 < d/(3*A) by positivity))
  filter_upwards [he, eventually_ge_atTop 1] with k hsmall hk1
  intro P hP hPk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hx0 : (0 : ℝ) < (k : ℝ)+2 := by positivity
  have hL : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
  have hs : log ((k : ℝ)+2) ≤ d/(3*A)*((k : ℝ)+2)^η := by
    simpa only [Real.norm_eq_abs, abs_of_pos hL,
      abs_of_pos (rpow_pos_of_pos hx0 η)] using hsmall
  have hdens : d/log ((k : ℝ)+2) ≤ density P := by
    simpa only [d, density, one_div] using
      WeightedMertens.prime_set_density_lower P hP k hPk
  have hden : d ≤ density P * log ((k : ℝ)+2) := (div_le_iff₀ hL).mp hdens
  have hvar := coveredFraction_bound P hP k (by omega)
  have hδ := density_pos P hP
  have hv0 := void_nonneg P k
  have hvupper : coveredFraction P k ≤ log ((k : ℝ)+2)/(d*k) := by
    apply (le_div_iff₀ (mul_pos hd hk0)).mpr
    have hb := mul_le_mul_of_nonneg_right hden (mul_nonneg hk0.le hv0)
    have hc := mul_le_mul_of_nonneg_right
      (show (k : ℝ)*density P*coveredFraction P k ≤ 1 by linarith) hL.le
    nlinarith only [hb,hc]
  have hvupper' : coveredFraction P k ≤ 3*log ((k : ℝ)+2)/(d*((k : ℝ)+2)) := by
    apply hvupper.trans
    apply (div_le_div_iff₀ (mul_pos hd hk0) (mul_pos hd hx0)).mpr
    have hh := mul_le_mul_of_nonneg_left (show (k : ℝ)+2 ≤ 3*k by linarith)
      (mul_nonneg hd.le hL.le)
    nlinarith only [hh]
  have hvfinal : coveredFraction P k ≤ ((k : ℝ)+2)^η/(A*((k : ℝ)+2)) := by
    apply hvupper'.trans
    apply (div_le_div_iff₀ (mul_pos hd hx0) (mul_pos hA hx0)).mpr
    have hs' := (le_div_iff₀ (show 0 < 3*A by positivity)).mp
      (show log ((k : ℝ)+2) ≤ (d*((k : ℝ)+2)^η)/(3*A) by
        simpa only [div_mul_eq_mul_div] using hs)
    have hh := mul_le_mul_of_nonneg_right hs' hx0.le
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hvfinal
    (show 0 ≤ A*((k : ℝ)+2)^α by positivity)
  have heq : (A*((k : ℝ)+2)^α) * (((k : ℝ)+2)^η/(A*((k : ℝ)+2))) =
      exp (-(η*log ((k : ℝ)+2))) := by
    have hxne := hx0.ne'
    calc
      _ = ((k : ℝ)+2)^α * ((k : ℝ)+2)^η / ((k : ℝ)+2) := by field_simp
      _ = ((k : ℝ)+2)^(α+η-1) := by
        rw [← rpow_add hx0, rpow_sub hx0, rpow_one]
      _ = ((k : ℝ)+2)^(-η) := by congr 1; dsimp [η]; ring
      _ = _ := by rw [rpow_def_of_pos hx0]; congr 1; ring
  rw [heq] at hh
  exact hh

lemma local_dyadic_iteration (P : Finset ℕ) (k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ m : ℕ, k ≤ m → coveredFraction P (2*m) ≤ a*coveredFraction P m^2)
    (j : ℕ) : a*coveredFraction P (2^j*k) ≤ (a*coveredFraction P k)^(2^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hkj : k ≤ 2^j*k := Nat.le_mul_of_pos_left k (by positivity)
    have hh := mul_le_mul_of_nonneg_left (h (2^j*k) hkj) ha
    have hh' : a*coveredFraction P (2*(2^j*k)) ≤
        (a*coveredFraction P (2^j*k))^2 := by nlinarith only [hh]
    have hp := pow_le_pow_left₀ (mul_nonneg ha (void_nonneg P _)) ih 2
    have he : ((a*coveredFraction P k)^(2^j))^2 =
        (a*coveredFraction P k)^(2^(j+1)) := by rw [← pow_mul, pow_succ]
    rw [he] at hp
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh'.trans hp

lemma power_loss_dyadic_tail {A α : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α)
    (h : PowerLossDyadicVoidBound A α) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k j : ℕ) (hk : P.card ≤ k)
    (hbase : (A*((k : ℝ)+2)^α)*coveredFraction P k ≤
      exp (-((1-α)/2*log ((k : ℝ)+2)))) :
    coveredFraction P (2^j*k) ≤
      exp (-((1-α)/2*log ((k : ℝ)+2)*(2 : ℝ)^j)) := by
  let a := A*((k : ℝ)+2)^α
  have hpow : 1 ≤ ((k : ℝ)+2)^α := one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hα
  have ha : 1 ≤ a := by dsimp [a]; nlinarith
  have hstep : ∀ m : ℕ, k ≤ m → coveredFraction P (2*m) ≤ a*coveredFraction P m^2 := by
    intro m hm
    apply (h P hP m (hk.trans hm)).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ A)
    apply rpow_le_rpow (by positivity) _ hα
    have hh : (P.card : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hi := local_dyadic_iteration P k a (by linarith) hstep j
  have hp := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ a) (void_nonneg P k))
    hbase (2^j)
  have hv := mul_le_mul_of_nonneg_right ha (void_nonneg P (2^j*k))
  simp only [one_mul] at hv
  calc
    _ ≤ (a*coveredFraction P k)^(2^j) := hv.trans hi
    _ ≤ (exp (-((1-α)/2*log ((k : ℝ)+2))))^(2^j) := hp
    _ = _ := by rw [← exp_nat_mul]; congr 1; push_cast; ring

/-- CONDITIONAL: every fixed sublinear power loss per long doubling step
still implies a fixed quadratic bound. The interval constant depends on α. -/
theorem eventually_quadratic_of_power_loss_dyadic {A α : ℝ}
    (hA : 1 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h : PowerLossDyadicVoidBound A α) (D : ℕ) (hD : 56 < (1-α)*D) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ D*k^2 := by
  have hDpos : 0 < D := by
    by_contra hn
    have hz : D = 0 := by omega
    norm_num [hz] at hD
  have hη : 0 < (1-α)/2 := by linarith
  filter_upwards [eventually_power_scaled_void_base A α (by linarith) hα1,
    eventually_ge_atTop (max D 1)] with k hbase hkbig
  have hDk : D ≤ k := (le_max_left _ _).trans hkbig
  have hk1 : 1 ≤ k := (le_max_right _ _).trans hkbig
  have hk : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let j := Nat.log 2 (D*k)
  have hlow : D*k < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) (D*k)
  have hupp : 2^j ≤ D*k := Nat.pow_log_le_self 2 (by positivity : D*k ≠ 0)
  let m := 2^j*k
  have hm : m ≤ D*k^2 := by dsimp [m]; nlinarith
  apply (jacobsthalFunction_le_iff k (D*k^2)).mpr
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcov⟩ := (not_isJacobsthalBound_iff_cover k (D*k^2)).mp hbad
  obtain ⟨Q,s,hQ,hQk,hcap,hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have htail := power_loss_dyadic_tail hA hα0 h Q hQ k j hQk (hbase Q hQ hQk)
  have hL : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
  have hbudget : (k : ℝ)*log (((k : ℝ)+2)^14) <
      (1-α)/2*log ((k : ℝ)+2)*(2 : ℝ)^j := by
    have hlo : (D : ℝ)*k < 2*(2 : ℝ)^j := by
      have hh : D*k < 2*2^j := by simpa only [pow_succ, Nat.mul_comm] using hlow
      exact_mod_cast hh
    have h1 := mul_lt_mul_of_pos_right hD hkR
    have h2 := mul_lt_mul_of_pos_left hlo (show 0 < 1-α by linarith)
    have hcoef : 14*(k : ℝ) < (1-α)/2*(2 : ℝ)^j := by nlinarith only [h1,h2]
    have hh := mul_lt_mul_of_pos_right hcoef hL
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hh]
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by linarith : (1 : ℝ) ≤ (k : ℝ)+2))
    (fun q hq => scaled_quadratic_cap hDk (hcap q hq)) htail hbudget s
  obtain ⟨q,hq,hxq⟩ := hcov' x (hx.trans_le hm)
  exact havoid q hq hxq

/-- This has precisely the original conclusion, but retains the unproved
dyadic premise. It is not an unconditional settlement of Erdős 970. -/
theorem quadratic_bound_of_power_loss_dyadic {A α : ℝ}
    (hA : 1 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h : PowerLossDyadicVoidBound A α) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C*k^2 := by
  obtain ⟨D,hD⟩ := exists_nat_gt (56/(1-α))
  have hD' : 56 < (1-α)*D := by
    have hh := (div_lt_iff₀ (show 0 < 1-α by linarith)).mp hD
    linarith
  have hDpos : 0 < D := by
    by_contra hn
    have hz : D = 0 := by omega
    norm_num [hz] at hD'
  exact quadratic_bound_of_eventually_scaled hDpos
    (eventually_quadratic_of_power_loss_dyadic hA hα0 hα1 h D hD')

lemma power_loss_zero_of_long_dyadic {A : ℝ} (h : LongDyadicVoidBound A) :
    PowerLossDyadicVoidBound A 0 := by
  intro P hP m hm
  simpa only [rpow_zero, mul_one] using h P hP m hm

/-- In particular, allowing a square-root budget loss would still give the
same explicit eventual constant 128 as the earlier constant-loss criterion. -/
theorem eventually_quadratic_of_sqrt_dyadic {A : ℝ} (hA : 1 ≤ A)
    (h : PowerLossDyadicVoidBound A (1/2)) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ 128*k^2 :=
  eventually_quadratic_of_power_loss_dyadic hA (by norm_num) (by norm_num) h
    128 (by norm_num)

#print axioms eventually_power_scaled_void_base
#print axioms power_loss_dyadic_tail
#print axioms quadratic_bound_of_power_loss_dyadic
#print axioms eventually_quadratic_of_sqrt_dyadic
end Erdos970.GapAverages
