import Submission.SharperLinearExposure
import Submission.PolynomialLossDyadicReduction

/-! A fractional-power long-doubling criterion. The nonlinear premise is
explicitly UNPROVED. Its conclusion is the unchanged quadratic conjecture. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1000000

/-- A weaker candidate than squared-probability doubling: the effective
exponent on the shorter-block probability is only 3/2. -/
def SquareCubicVoidBound (A α : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, P.card ≤ m →
    coveredFraction P (2*m)^2 ≤
      (A*((P.card : ℝ)+2)^α)*coveredFraction P m^3

lemma square_cubic_chain (f : ℕ → ℝ) (k m : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hm : k ≤ m)
    (hs : ∀ n, k ≤ n → f (2*n)^2 ≤ f n^3) (j : ℕ) :
    f (2^j*m)^(2^j) ≤ f m^(3^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hkm : k ≤ 2^j*m := hm.trans (Nat.le_mul_of_pos_left m (by positivity))
    have h1 := pow_le_pow_left₀ (sq_nonneg _) (hs _ hkm) (2^j)
    have h2 := pow_le_pow_left₀ (pow_nonneg (hf _) _) ih 3
    calc
      _ = (f (2*(2^j*m))^2)^(2^j) := by
        rw [← pow_mul]
        congr 2 <;> simp [pow_succ] <;> ring
      _ ≤ (f (2^j*m)^3)^(2^j) := h1
      _ = (f (2^j*m)^(2^j))^3 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ ≤ (f m^(3^j))^3 := h2
      _ = _ := by rw [← pow_mul, pow_succ]

lemma square_cubic_four (f : ℕ → ℝ) (k m : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hm : k ≤ m)
    (hs : ∀ n, k ≤ n → f (2*n)^2 ≤ f n^3) (h1 : f m ≤ 1) :
    f (16*m) ≤ f m^5 := by
  have hc := square_cubic_chain f k m hf hm hs 4
  norm_num only [show (2 : ℕ)^4=16 by norm_num, show (3 : ℕ)^4=81 by norm_num] at hc
  have hp : f m^81 ≤ f m^80 := pow_le_pow_of_le_one (hf _) h1 (by omega)
  apply (pow_le_pow_iff_left₀ (hf _) (pow_nonneg (hf _) 5) (by norm_num : 16 ≠ 0)).mp
  simpa only [← pow_mul, show (5 : ℕ)*16=80 by omega] using hc.trans hp

lemma square_cubic_iteration (f : ℕ → ℝ) (k : ℕ)
    (hf : ∀ n, 0 ≤ f n) (h1 : f k ≤ 1)
    (hs : ∀ n, k ≤ n → f (2*n)^2 ≤ f n^3) (j : ℕ) :
    f (16^j*k) ≤ f k^(5^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hkm : k ≤ 16^j*k := Nat.le_mul_of_pos_left k (by positivity)
    have hone : f (16^j*k) ≤ 1 := ih.trans (pow_le_one₀ (hf k) h1)
    have hh := square_cubic_four f k (16^j*k) hf hkm hs hone
    have hp := pow_le_pow_left₀ (hf _) ih 5
    calc
      _ = f (16*(16^j*k)) := by congr 1; rw [pow_succ]; ring
      _ ≤ f (16^j*k)^5 := hh
      _ ≤ (f k^(5^j))^5 := hp
      _ = _ := by rw [← pow_mul, pow_succ]

lemma eventually_fractional_log_budget (A α : ℝ) (hα : 0 ≤ α) :
    ∀ᶠ k : ℕ in atTop,
      log A + (α+1/2)*log ((k : ℝ)+2) ≤ (k : ℝ)^(37/80 : ℝ)/800 := by
  let c := |log A|+2*α+1
  have hc : 0 < c := by dsimp [c]; positivity
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 37/80)).def
      (show (0 : ℝ) < 1/(800*c) by positivity))
  filter_upwards [hs, eventually_ge_atTop 4] with k hs hk
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl : 0 ≤ log (k : ℝ) := log_nonneg (by linarith)
  have hl1 : 1 ≤ log (k : ℝ) := by
    have h4 : (1 : ℝ) ≤ log 4 := by
      rw [show (4 : ℝ)=2^2 by norm_num, log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [log_two_gt_d9]
    exact h4.trans (log_le_log (by norm_num) hkR)
  have hs' : log (k : ℝ) ≤ (k : ℝ)^(37/80 : ℝ)/(800*c) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl,
      abs_of_pos (rpow_pos_of_pos hk0 (37/80)), one_div, inv_mul_eq_div] using hs
  have hcs : c*log (k : ℝ) ≤ (k : ℝ)^(37/80 : ℝ)/800 := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 800*c by positivity)).mp hs'
    nlinarith only [hh]
  have hl2 : log ((k : ℝ)+2) ≤ 2*log (k : ℝ) := by
    have hh := log_le_log (by positivity : (0 : ℝ) < (k : ℝ)+2)
      (show (k : ℝ)+2 ≤ (k : ℝ)^2 by nlinarith only [hkR])
    simpa only [log_pow, Nat.cast_ofNat] using hh
  have ha := mul_le_mul_of_nonneg_left hl1 (abs_nonneg (log A))
  have hh := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ α+1/2 by linarith)
  have hla := le_abs_self (log A)
  dsimp only [c] at hcs
  nlinarith only [hcs,ha,hh,hla]

/-- Polynomial factors can be absorbed while retaining a stretched power. -/
lemma eventually_fractional_scaled_void_base (A α : ℝ) (hA : 0 < A) (hα : 0 ≤ α) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      (A*((k : ℝ)+2)^α)*coveredFraction P k ≤ exp (-((k : ℝ)^(37/80 : ℝ)/800)) := by
  filter_upwards [eventually_sharper_linear_stretched_void,
    eventually_fractional_log_budget A α hα] with k hvoid hlog
  intro P hP hPk
  have hscale := mul_le_mul_of_nonneg_left (hvoid P hP hPk)
    (show 0 ≤ A*((k : ℝ)+2)^α by positivity)
  apply hscale.trans
  have he : A*((k : ℝ)+2)^α = exp (log A+α*log ((k : ℝ)+2)) := by
    rw [exp_add, exp_log hA, rpow_def_of_pos (by positivity)]
    congr 1
    congr 1
    ring
  rw [he, ← exp_add]
  have hl : 0 ≤ log ((k : ℝ)+2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  exact exp_le_exp.mpr (by nlinarith only [hlog,hl])


lemma square_cubic_tail {A α : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α)
    (h : SquareCubicVoidBound A α) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k j : ℕ) (hk : P.card ≤ k)
    (hbase : (A*((k : ℝ)+2)^α)*coveredFraction P k ≤ exp (-((k : ℝ)^(37/80 : ℝ)/800))) :
    coveredFraction P (16^j*k) ≤ exp (-((k : ℝ)^(37/80 : ℝ)*(5 : ℝ)^j/800)) := by
  let a := A*((k : ℝ)+2)^α
  have hpow : 1 ≤ ((k : ℝ)+2)^α := one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hα
  have ha : 1 ≤ a := by dsimp [a]; nlinarith only [hA,hpow]
  let f := fun n => a*coveredFraction P n
  have hf : ∀ n, 0 ≤ f n := fun n => mul_nonneg (by linarith) (void_nonneg P n)
  have hstep : ∀ m, k ≤ m → f (2*m)^2 ≤ f m^3 := by
    intro m hm
    have hh := h P hP m (hk.trans hm)
    have hcoef : A*((P.card : ℝ)+2)^α ≤ a := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ A)
      apply rpow_le_rpow (by positivity) _ hα
      have hh : (P.card : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hv := hh.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg (void_nonneg P m) 3))
    have hs := mul_le_mul_of_nonneg_left hv (sq_nonneg a)
    dsimp only [f]
    nlinarith only [hs]
  have h1 : f k ≤ 1 := hbase.trans (exp_le_one_iff.mpr (by have := rpow_nonneg (Nat.cast_nonneg k) (37/80 : ℝ); linarith))
  have hi := square_cubic_iteration f k hf h1 hstep j
  have hp := pow_le_pow_left₀ (hf _) hbase (5^j)
  have hv := mul_le_mul_of_nonneg_right ha (void_nonneg P (16^j*k))
  simp only [one_mul] at hv
  calc
    _ ≤ f k^(5^j) := hv.trans hi
    _ ≤ (exp (-((k : ℝ)^(37/80 : ℝ)/800)))^(5^j) := hp
    _ = _ := by rw [← exp_nat_mul]; congr 1; push_cast; ring

lemma fractional_iteration_rate (k j : ℕ) (hk : 0 < k) (hkj : k ≤ 16*16^j) :
    (k : ℝ)^(41/40 : ℝ) ≤ 16*(k : ℝ)^(37/80 : ℝ)*(5 : ℝ)^j := by
  have hbase : (16 : ℕ)^9 ≤ 5^16 := by norm_num
  have hi := Nat.pow_le_pow_left hbase j
  have hn : k^9 ≤ 16^16*(5^j)^16 := by
    calc
      _ ≤ (16*16^j)^9 := Nat.pow_le_pow_left hkj 9
      _ = 16^9*(16^9)^j := by rw [mul_pow, ← pow_mul, ← pow_mul]; congr 2; omega
      _ ≤ 16^16*(5^16)^j := Nat.mul_le_mul (by norm_num) hi
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 2; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have he : ((k : ℝ)^(9/16 : ℝ))^16 = (k : ℝ)^9 := by
    rw [← rpow_natCast _ 16, ← rpow_mul hk0.le]
    norm_num
  have hr : (k : ℝ)^(9/16 : ℝ) ≤ 16*(5 : ℝ)^j := by
    apply (pow_le_pow_iff_left₀ (rpow_nonneg hk0.le _) (by positivity)
      (by norm_num : 16 ≠ 0)).mp
    rw [he, mul_pow]
    exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left hr (rpow_nonneg hk0.le (37/80 : ℝ))
  rw [← rpow_add hk0] at hh
  norm_num only [show (37/80 : ℝ)+9/16=41/40 by norm_num] at hh
  nlinarith only [hh]

lemma eventually_fractional_entropy :
    ∀ᶠ k : ℕ in atTop, (k : ℝ)*log (((k : ℝ)+2)^14) < (k : ℝ)^(41/40 : ℝ)/12800 := by
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/40)).def
      (show (0 : ℝ) < 1/716800 by norm_num))
  filter_upwards [hs, eventually_ge_atTop 4] with k hs hk
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hl : 0 ≤ log (k : ℝ) := log_nonneg (by linarith)
  have hs' : log (k : ℝ) ≤ (k : ℝ)^(1/40 : ℝ)/716800 := by
    have hp0 : 0 ≤ (k : ℝ)^(1/40 : ℝ) := rpow_nonneg hk0.le _
    simp only [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hp0] at hs
    convert hs using 1 <;> ring
  have hl2 : log ((k : ℝ)+2) ≤ 2*log (k : ℝ) := by
    have hh := log_le_log (by positivity : (0 : ℝ) < (k : ℝ)+2)
      (show (k : ℝ)+2 ≤ (k : ℝ)^2 by nlinarith only [hkR])
    simpa only [log_pow, Nat.cast_ofNat] using hh
  have h1 := mul_le_mul_of_nonneg_left hl2 hk0.le
  have h2 := mul_le_mul_of_nonneg_left hs' hk0.le
  have he : (k : ℝ)*(k : ℝ)^(1/40 : ℝ) = (k : ℝ)^(41/40 : ℝ) := by
    have hh := rpow_add hk0 (1 : ℝ) (1/40)
    norm_num at hh
    exact hh.symm
  have hp : 0 < (k : ℝ)^(41/40 : ℝ) := rpow_pos_of_pos hk0 _
  rw [← mul_div_assoc, he] at h2
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [h1,h2,hp]

/-- CONDITIONAL: square–cubic long doubling with any fixed polynomial loss
would suffice. The displayed nonlinear premise remains an explicit hypothesis. -/
theorem eventually_quadratic_of_square_cubic {A α : ℝ}
    (hA : 1 ≤ A) (hα : 0 ≤ α) (h : SquareCubicVoidBound A α) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ k^2 := by
  filter_upwards [eventually_fractional_scaled_void_base A α (by linarith) hα,
    eventually_fractional_entropy, eventually_ge_atTop 4] with k hbase hent hk4
  have hk : 0 < k := by omega
  let j := Nat.log 16 k
  have hlow : k < 16^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hupp : 16^j ≤ k := Nat.pow_log_le_self 16 hk.ne'
  have hkj : k ≤ 16*16^j := by simpa only [pow_succ, Nat.mul_comm] using hlow.le
  have hr := fractional_iteration_rate k j hk hkj
  let m := 16^j*k
  have hm : m ≤ k^2 := by dsimp only [m]; nlinarith
  apply (jacobsthalFunction_le_iff k (k^2)).mpr
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcov⟩ := (not_isJacobsthalBound_iff_cover k (k^2)).mp hbad
  obtain ⟨Q,s,hQ,hQk,hcap,hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have htail := square_cubic_tail hA hα h Q hQ k j hQk (hbase Q hQ hQk)
  have hbudget : (k : ℝ)*log (((k : ℝ)+2)^14) < (k : ℝ)^(37/80 : ℝ)*(5 : ℝ)^j/800 := by
    nlinarith only [hent,hr]
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ)+2))
    (fun q hq => scaled_quadratic_cap (by omega : 1 ≤ k) (by simpa only [one_mul] using hcap q hq))
    htail hbudget s
  obtain ⟨q,hq,hxq⟩ := hcov' x (hx.trans_le hm)
  exact havoid q hq hxq

/-- Precisely the original conclusion, with the unproved square–cubic
hypothesis retained. This theorem is not a settlement of Erdős 970. -/
theorem quadratic_bound_of_square_cubic {A α : ℝ}
    (hA : 1 ≤ A) (hα : 0 ≤ α) (h : SquareCubicVoidBound A α) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C*k^2 := by
  apply quadratic_bound_of_eventually_scaled (D := 1) (by norm_num)
  simpa only [one_mul] using eventually_quadratic_of_square_cubic hA hα h

#print axioms square_cubic_tail
#print axioms eventually_quadratic_of_square_cubic
#print axioms quadratic_bound_of_square_cubic
end Erdos970.GapAverages
