import Submission.IntervalReciprocalTotient

/-!
# Direct reciprocal-totient mass estimates on exponential blocks

The endpoint error tends to zero for each pair of fixed positive block
indices. These estimates do not assert the shifted-prime lower bound.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma exp_primeTotientMass_scale_upper (E : ℕ) (hE : 1 ≤ E) :
    Real.exp (primeTotientMass (progressionScaleN E)) ≤
      Real.exp 1024*(E : ℝ)^8 := by
  have hEpos : (0 : ℝ) < E := by exact_mod_cast hE
  have h := Real.exp_le_exp.mpr (primeTotientMass_scale_upper E hE)
  rw [Real.exp_add,show (8 : ℝ)=((8 : ℕ) : ℝ) by norm_num,
    Real.exp_nat_mul,Real.exp_log hEpos] at h
  exact h

lemma two_mul_pow_pred_eq (e : ℕ) (he : 1 ≤ e) :
    2*2^(e-1) = (2 : ℕ)^e := by
  rw [← pow_succ',Nat.succ_eq_add_one,Nat.sub_add_cancel he]

noncomputable def evenBlockMass (a b m : ℕ) : ℝ :=
  ∑ n ∈ Icc (2^(64*a*m)+1) (2^(64*b*m)) with Even n,
    1/(n.totient : ℝ)

lemma evenBlockMass_upper (a b m : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : 1 ≤ m) :
    evenBlockMass a b m ≤
      (4/3 : ℝ)*64*((b : ℝ)-a)*m*Real.log 2 +
        (Real.exp 1024*(b : ℝ)^8)*((m : ℝ)^8/(2 : ℝ)^m) := by
  let A : ℕ := 2^(64*a*m-1)
  let B : ℕ := 2^(64*b*m-1)
  have ham : m ≤ a*m := Nat.le_mul_of_pos_left m ha
  have hbm : m ≤ b*m := ham.trans (Nat.mul_le_mul_right m hab)
  have haexp : 1 ≤ 64*a*m := by nlinarith only [ham,hm]
  have hbexp : 1 ≤ 64*b*m := by nlinarith only [hbm,hm]
  have hAB : A ≤ B := by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 64 hab)) 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have htwoA : 2*A=2^(64*a*m) := two_mul_pow_pred_eq _ haexp
  have htwoB : 2*B=2^(64*b*m) := two_mul_pow_pred_eq _ hbexp
  have hlog : Real.log ((B : ℝ)/A) = 64*((b : ℝ)-a)*m*Real.log 2 := by
    rw [Real.log_div (by exact_mod_cast hB.ne' : (B : ℝ) ≠ 0)
      (by exact_mod_cast hA.ne' : (A : ℝ) ≠ 0)]
    simp only [A,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,
      Nat.cast_sub haexp,Nat.cast_sub hbexp,Nat.cast_mul,Nat.cast_one]
    ring
  have hBcap : B ≤ progressionScaleN (b*m) := by
    change 2^(64*b*m-1) ≤ 2^(64*(b*m))
    apply Nat.pow_le_pow_right (by decide)
    simpa only [mul_assoc] using Nat.sub_le (64*b*m) 1
  have hmass : Real.exp (primeTotientMass B) ≤ Real.exp 1024*(b : ℝ)^8*(m : ℝ)^8 := by
    have h := (Real.exp_le_exp.mpr (primeTotientMass_mono hBcap)).trans
      (exp_primeTotientMass_scale_upper (b*m) (by omega))
    simpa only [Nat.cast_mul,mul_pow,mul_assoc] using h
  have hApow : (2 : ℝ)^m ≤ A := by
    have hn : 2^m ≤ A := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [A]
      have hs := Nat.sub_add_cancel haexp
      nlinarith only [ham,hm,hs]
    exact_mod_cast hn
  have herr : Real.exp (primeTotientMass B)/(A : ℝ) ≤
      (Real.exp 1024*(b : ℝ)^8)*((m : ℝ)^8/(2 : ℝ)^m) := by
    calc
      _ ≤ (Real.exp 1024*(b : ℝ)^8*(m : ℝ)^8)/(2 : ℝ)^m := by
        exact div_le_div₀ (by positivity) hmass (by positivity) hApow
      _ = _ := by ring
  have hh := even_reciprocal_totient_interval_le A B hA hAB
  rw [htwoA,htwoB,hlog] at hh
  change evenBlockMass a b m ≤ _ at hh
  exact hh.trans (by nlinarith only [herr])

lemma eventually_evenBlockMass_upper (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      evenBlockMass a b m ≤ (4/3 : ℝ)*64*((b : ℝ)-a)*m*Real.log 2+η := by
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 8
    (by norm_num : (1 : ℝ) < 2)).const_mul (Real.exp 1024*(b : ℝ)^8)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hη),eventually_ge_atTop 1] with m he hm
  exact (evenBlockMass_upper a b m ha hab hm).trans (_root_.add_le_add le_rfl he)

end Erdos821.Sieve
