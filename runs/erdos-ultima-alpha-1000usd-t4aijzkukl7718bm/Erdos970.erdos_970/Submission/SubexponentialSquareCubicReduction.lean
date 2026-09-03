import Submission.ArbitrarySubcriticalExposure
import Submission.SquareCubicDyadicReduction

/-! A conditional quadratic reduction allowing loss exp(C*k^beta), beta<1,
in square-cubic doubling. The nonlinear premise is NOT proved here. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- A candidate correlation inequality, with a sublinear-power exponential
loss in the cardinality budget. This is an explicit unproved premise. -/
def SubexponentialSquareCubicVoidBound (C β : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, P.card ≤ m →
    coveredFraction P (2*m)^2 ≤ exp (C*(P.card : ℝ)^β)*coveredFraction P m^3

lemma square_cubic_scaled_tail (P : Finset ℕ) (m j : ℕ) (a B : ℝ)
    (ha : 1 ≤ a) (hB : 0 ≤ B)
    (hstep : ∀ n, m ≤ n → coveredFraction P (2*n)^2 ≤ a*coveredFraction P n^3)
    (hbase : a*coveredFraction P m ≤ exp (-B)) :
    coveredFraction P (16^j*m) ≤ exp (-B*(5 : ℝ)^j) := by
  let f := fun n => a*coveredFraction P n
  have ha0 : 0 ≤ a := by linarith
  have hf : ∀ n, 0 ≤ f n := fun n => mul_nonneg ha0 (void_nonneg P n)
  have hs : ∀ n, m ≤ n → f (2*n)^2 ≤ f n^3 := by
    intro n hn
    have hh := mul_le_mul_of_nonneg_left (hstep n hn) (sq_nonneg a)
    dsimp only [f]
    nlinarith only [hh]
  have h1 : f m ≤ 1 := hbase.trans (exp_le_one_iff.mpr (by linarith))
  have hi := square_cubic_iteration f m hf h1 hs j
  have hp := pow_le_pow_left₀ (hf _) hbase (5^j)
  have hv := mul_le_mul_of_nonneg_right ha (void_nonneg P (16^j*m))
  simp only [one_mul] at hv
  calc
    _ ≤ f m^(5^j) := hv.trans hi
    _ ≤ (exp (-B))^(5^j) := hp
    _ = _ := by rw [← exp_nat_mul]; congr 1; push_cast; ring

lemma eventually_scaled_power_seed (C β : ℝ) (b : ℕ)
    (hb : 1 ≤ b) (hβ : (b : ℝ)*β < (b : ℝ)-17/32) :
    ∀ᶠ t : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ t^b →
      exp (C*((t^b : ℕ) : ℝ)^β)*coveredFraction P (t^(2*b-1)) ≤
        exp (-((t : ℝ)^((b : ℝ)-17/32)/800)) := by
  let q : ℝ := (b : ℝ)-17/32
  let a : ℕ := 2*b-1
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have ha : 0 < a := by dsimp [a]; omega
  have haR : (a : ℝ) = 2*(b : ℝ)-1 := by dsimp [a]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hq : 0 < q := by dsimp [q]; linarith
  have hσ : q/(a : ℝ) < 1/2 := by
    rw [div_lt_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a),haR]
    dsimp [q]
    linarith
  have hseed := (tendsto_pow_atTop ha.ne').eventually (eventually_subhalf_linear_void (q/a) hσ)
  have hgap : 0 < q-(b : ℝ)*β := sub_pos.mpr hβ
  have hscale := tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop hgap).eventually (eventually_ge_atTop (800*C)))
  filter_upwards [hseed,hscale,eventually_ge_atTop 1] with t hs hc ht
  intro P hP hPk
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hba : b ≤ a := by dsimp [a]; omega
  have hcard : P.card ≤ t^a := hPk.trans (Nat.pow_le_pow_right (by omega) hba)
  have hv := hs P hP hcard
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have heq : ((t^a : ℕ) : ℝ)^(q/(a : ℝ)) = (t : ℝ)^q := by
    rw [Nat.cast_pow,← rpow_natCast (t : ℝ) a,← rpow_mul ht0.le,
      mul_div_cancel₀ q ha0]
  rw [heq] at hv
  have heqB : ((t^b : ℕ) : ℝ)^β = (t : ℝ)^((b : ℝ)*β) := by
    rw [Nat.cast_pow,← rpow_natCast (t : ℝ) b,← rpow_mul ht0.le]
  have hc' := mul_le_mul_of_nonneg_right hc (rpow_nonneg ht0.le ((b : ℝ)*β))
  rw [← rpow_add ht0,sub_add_cancel] at hc'
  have hc'' : C*(((t^b : ℕ) : ℝ)^β) ≤ (t : ℝ)^q/800 := by
    rw [heqB]
    nlinarith only [hc']
  apply (mul_le_mul_of_nonneg_left hv (exp_pos _).le).trans
  rw [← exp_add]
  exact exp_le_exp.mpr (by linarith only [hc''])

lemma sixteenth_iteration_growth (t j : ℕ) (ht : 0 < t) (htj : t ≤ 16*16^j) :
    (t : ℝ)^(9/16 : ℝ) ≤ 16*(5 : ℝ)^j := by
  have hbase : (16 : ℕ)^9 ≤ 5^16 := by norm_num
  have hi := Nat.pow_le_pow_left hbase j
  have hn : t^9 ≤ 16^16*(5^j)^16 := by
    calc
      _ ≤ (16*16^j)^9 := Nat.pow_le_pow_left htj 9
      _ = 16^9*(16^9)^j := by rw [mul_pow, ← pow_mul, ← pow_mul]; congr 2; omega
      _ ≤ 16^16*(5^16)^j := Nat.mul_le_mul (by norm_num) hi
      _ = _ := by rw [← pow_mul, ← pow_mul]; congr 2; omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have he : ((t : ℝ)^(9/16 : ℝ))^16 = (t : ℝ)^9 := by
    rw [← rpow_natCast _ 16, ← rpow_mul ht0.le]
    norm_num
  apply (pow_le_pow_iff_left₀ (rpow_nonneg ht0.le _) (by positivity)
    (by norm_num : 16 ≠ 0)).mp
  rw [he, mul_pow]
  exact_mod_cast hn

lemma eventually_power_entropy (b : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      ((t^b : ℕ) : ℝ)*log ((((t^b : ℕ) : ℝ)+2)^14) <
        (t : ℝ)^((b : ℝ)+1/32)/12800 := by
  let c : ℝ := 14*((b : ℝ)+2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/32)).def
      (show (0 : ℝ) < 1/(25600*c) by positivity))
  filter_upwards [hs,eventually_ge_atTop 2] with t hs ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hl : 0 ≤ log (t : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  have hs' : log (t : ℝ) ≤ (t : ℝ)^(1/32 : ℝ)/(25600*c) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hl,
      abs_of_pos (rpow_pos_of_pos ht0 _),one_div,inv_mul_eq_div] using hs
  have h1 := log_power_add_two_le t b ht
  have h2 := mul_le_mul_of_nonneg_left hs' hc.le
  have h2' : c*log (t : ℝ) ≤ (t : ℝ)^(1/32 : ℝ)/25600 := by
    convert h2 using 1
    field_simp
  have h3 : log ((((t^b : ℕ) : ℝ)+2)^14) ≤ (t : ℝ)^(1/32 : ℝ)/25600 := by
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp only [c] at h2'
    linarith only [h1,h2']
  have hh := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (t^b))
  have he : ((t^b : ℕ) : ℝ)*(t : ℝ)^(1/32 : ℝ) = (t : ℝ)^((b : ℝ)+1/32) := by
    rw [Nat.cast_pow,← rpow_natCast (t : ℝ) b,← rpow_add ht0]
  rw [← mul_div_assoc,he] at hh
  have hp : 0 < (t : ℝ)^((b : ℝ)+1/32) := rpow_pos_of_pos ht0 _
  linarith only [hh,hp]

/-- CONDITIONAL: on the power budgets t^b the unproved correlation estimate
would exclude every phase, using a starting interval t^(2b-1). -/
theorem eventually_quadratic_power_budget_of_subexponential_square_cubic
    {C β : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β)
    (h : SubexponentialSquareCubicVoidBound C β)
    (b : ℕ) (hb : 1 ≤ b) (hβ : (b : ℝ)*β < (b : ℝ)-17/32) :
    ∀ᶠ t : ℕ in atTop, jacobsthalFunction (t^b) ≤ (t^b)^2 := by
  filter_upwards [eventually_scaled_power_seed C β b hb hβ,
    eventually_power_entropy b,eventually_ge_atTop 2] with t hbase hent ht
  have htpos : 0 < t := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast htpos
  let K := t^b
  let m := t^(2*b-1)
  let j := Nat.log 16 t
  have hlow : t < 16^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have hupp : 16^j ≤ t := Nat.pow_log_le_self 16 htpos.ne'
  have htj : t ≤ 16*16^j := by simpa only [pow_succ,Nat.mul_comm] using hlow.le
  have hKm : K ≤ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : 16^j*m ≤ K^2 := by
    have hh := Nat.mul_le_mul_right m hupp
    apply hh.trans_eq
    dsimp only [m,K]
    rw [← pow_succ',← pow_mul]
    congr 1
    omega
  apply (jacobsthalFunction_le_iff K (K^2)).mpr
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcov⟩ := (not_isJacobsthalBound_iff_cover K (K^2)).mp hbad
  obtain ⟨Q,s,hQ,hQk,hcap,hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  let a := exp (C*(K : ℝ)^β)
  have ha : 1 ≤ a := one_le_exp_iff.mpr (mul_nonneg hC (rpow_nonneg (Nat.cast_nonneg K) β))
  have hstep : ∀ n, m ≤ n → coveredFraction Q (2*n)^2 ≤ a*coveredFraction Q n^3 := by
    intro n hn
    apply (h Q hQ n (hQk.trans (hKm.trans hn))).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (void_nonneg Q n) 3)
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hC
    exact rpow_le_rpow (Nat.cast_nonneg Q.card) (by exact_mod_cast hQk) hβ0
  have htail := square_cubic_scaled_tail Q m j a ((t : ℝ)^((b : ℝ)-17/32)/800) ha
    (by positivity) hstep (hbase Q hQ hQk)
  have hrate := sixteenth_iteration_growth t j htpos htj
  have hrate' := mul_le_mul_of_nonneg_left hrate
    (rpow_nonneg ht0.le ((b : ℝ)-17/32))
  rw [← rpow_add ht0,show (b : ℝ)-17/32+9/16=(b : ℝ)+1/32 by ring] at hrate'
  have hbudget : (K : ℝ)*log (((K : ℝ)+2)^14) <
      (t : ℝ)^((b : ℝ)-17/32)/800*(5 : ℝ)^j := by
    change (K : ℝ)*log (((K : ℝ)+2)^14) < (t : ℝ)^((b : ℝ)+1/32)/12800 at hent
    nlinarith only [hent,hrate']
  have hK : 1 ≤ K := Nat.one_le_pow _ _ htpos
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) K; linarith : (1 : ℝ) ≤ (K : ℝ)+2))
    (fun q hq => scaled_quadratic_cap hK (by simpa only [one_mul] using hcap q hq))
    (by simpa only [neg_mul] using htail) hbudget s
  obtain ⟨q,hq,hxq⟩ := hcov' x (hx.trans_le hm)
  exact havoid q hq hxq

/-- CONDITIONAL quadratic conclusion with the correlation premise retained.
The loss may be exp(C*k^beta) for any fixed beta strictly below one. -/
theorem quadratic_bound_of_subexponential_square_cubic
    {C β : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : SubexponentialSquareCubicVoidBound C β) :
    ∃ A > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ A*k^2 := by
  have hδ : 0 < 1-β := by linarith
  obtain ⟨b,hb⟩ := exists_nat_gt (1/(1-β))
  have hb' : 1 < (b : ℝ)*(1-β) := (div_lt_iff₀ hδ).mp hb
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := (div_pos (by norm_num) hδ).trans hb
    exact_mod_cast this
  have hβ : (b : ℝ)*β < (b : ℝ)-17/32 := by nlinarith only [hb']
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_quadratic_power_budget_of_subexponential_square_cubic hC hβ0 h b hb0 hβ)
  apply quadratic_bound_of_eventually_scaled (D := (2^b)^2) (by positivity)
  filter_upwards [eventually_ge_atTop ((N+1)^b)] with k hk
  have hkpos : 0 < k := (Nat.pow_pos (by omega : 0 < N+1)).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k b hkpos hb0
  have hNt : N+1 ≤ t := (Nat.pow_le_pow_iff_left hb0.ne').mp (hk.trans hkt)
  have hbound := (jacobsthalFunction_le_iff (t^b) ((t^b)^2)).mp (hN t (by omega))
  have hlen : (t^b)^2 ≤ (2^b)^2*k^2 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hroot 2
  apply (jacobsthalFunction_le_iff k ((2^b)^2*k^2)).mpr
  intro n hn hnk a
  obtain ⟨i,hi,hcop⟩ := hbound n hn (hnk.trans hkt) a
  exact ⟨i,hi.trans_le hlen,hcop⟩

#print axioms eventually_quadratic_power_budget_of_subexponential_square_cubic
#print axioms quadratic_bound_of_subexponential_square_cubic
end Erdos970.GapAverages
