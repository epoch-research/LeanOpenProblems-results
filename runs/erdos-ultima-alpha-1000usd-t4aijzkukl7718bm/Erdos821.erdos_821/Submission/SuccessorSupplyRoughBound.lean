import Submission.SuccessorSupplyScales

/-!
# A uniform rejected-prime budget below one

This combines the long- and short-cofactor estimates at fixed numerical
parameters. It is uniform over the actual prime cutoff and the smooth
progression modulus in their specified power intervals.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

theorem eventually_successor_supply_rough_bound :
    ∀ᶠ m : ℕ in atTop, ∀ X d : ℕ,
      independentN 400020 m ≤ X → X ≤ independentN 400021 m →
      independentN 200000 m ≤ d → d ≤ independentN 200004 m →
      d ∈ Nat.smoothNumbers (independentN 180000 m) →
        Real.log (X : ℝ)*((roughProgressionPrimes d (independentN 180000 m) X).card : ℝ) ≤
          (97/100 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
  obtain ⟨C,hC,K₀,hLong⟩ := exists_long_cofactor_hyperbolic_bound 1 99999 200003 3 10
    (by decide) (by decide) (by decide) (by decide) (by decide) (1/1000) (by norm_num)
  filter_upwards [eventually_successorLongBudget C,eventually_successorShortBudget,
    eventually_short_cofactor_dyadic_bound 100011 99999 (by decide) (by decide),
    eventually_successor_tail_error,eventually_ge_atTop (max 2 K₀)]
    with m hLB hSB hShort hTail hm
  intro X d hXlo hXhi hdlo hdhi hds
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := by omega
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 200000 m).trans_le hdlo
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hφ : (0 : ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  let H := X/d
  let F : ℝ := (d : ℝ)/(d.totient : ℝ)
  let L : ℝ := 64*400021*(m : ℝ)*Real.log 2
  let D : ℝ := 1/(128*90000*(m : ℝ)-1)-1/(128*99999*(m : ℝ)-1)
  let U : ℝ := (successorLeadingCoefficient/(Real.log 2)^2)*
      (Real.log 2*D+2*C/(128*90000*(m : ℝ))^2)+((1/1000)/(Real.log 2)^2)*D
  let V : ℝ := (1/75)*(1+1536*(m : ℝ)*Real.log 2)/((99999 : ℝ)*m*Real.log 2)^2
  have hH := successor_supply_quotient_bounds m X d hXlo hXhi hdlo hdhi
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hF1 : 1 ≤ F := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le d)
  have hHF : (H : ℝ)*F ≤ (X : ℝ)/(d.totient : ℝ) := by
    have hh : ((X/d : ℕ) : ℝ)*(d : ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X d
    simpa only [H,F,mul_div_assoc] using div_le_div_of_nonneg_right hh hφ.le
  have hHHF : (H : ℝ) ≤ (H : ℝ)*F := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hF1 (Nat.cast_nonneg H)
  have hHX : (H : ℝ) ≤ (X : ℝ)/(d.totient : ℝ) := hHHF.trans hHF
  have hlog : Real.log (X : ℝ) ≤ L := successor_supply_log_upper m X hXhi
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hD : 0 ≤ D := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by linarith : (0 : ℝ)<128*90000*(m : ℝ)-1) (by linarith)
  have hU : 0 ≤ U := by
    have hlead : 0 ≤ successorLeadingCoefficient := by norm_num [successorLeadingCoefficient]
    dsimp [U]
    positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hY : independentN 180000 m=2^(128*90000*m) := by
    rfl
  have hlong0 := hLong (128*90000*m) (128*9999*m) d H
    (by have := (le_max_right _ _).trans hm; omega) (by omega) hd (by
      rw [show 128*90000*m+128*9999*m=128*99999*m by omega]
      exact successor_supply_long_threshold m H hm2 hH.1)
  rw [show 128*90000*m+128*9999*m=128*99999*m by omega] at hlong0
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hlong0
  rw [show 128*90000*(m : ℝ)+128*9999*(m : ℝ)=128*99999*(m : ℝ) by ring] at hlong0
  have hlong : ((hyperbolicPrimePairPool d H (2^(128*90000*m)) (2^(128*99999*m))).card : ℝ) ≤
      (H : ℝ)*F*U := by
    have he : 0 ≤ ((1/1000 : ℝ)/(Real.log 2)^2)*D := by positivity
    have hExtra := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hF1 (Nat.cast_nonneg H)) he
    have hh := _root_.add_le_add (le_refl ((successorLeadingCoefficient*(H : ℝ)*F/(Real.log 2)^2)*
      (Real.log 2*D+2*C/(128*90000*(m : ℝ))^2))) hExtra
    apply hlong0.trans
    convert hh using 1 <;> dsimp [U,D,F,successorLeadingCoefficient] <;> ring
  have hlongW : Real.log (X : ℝ)*
      ((hyperbolicPrimePairPool d H (2^(128*90000*m)) (2^(128*99999*m))).card : ℝ) ≤
        (9/10 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
    have hh := mul_le_mul hlog hlong (Nat.cast_nonneg _) hL
    have hid : L*U=successorLongBudget C m := successorLongBudget_identity C m hm1
    have hnorm : L*((H : ℝ)*F*U)=(H : ℝ)*F*successorLongBudget C m := by rw [← hid]; ring
    rw [hnorm] at hh
    apply (hh.trans (mul_le_mul_of_nonneg_left hLB (show 0 ≤ (H : ℝ)*F by positivity))).trans
    have hlast := mul_le_mul_of_nonneg_left hHF (show (0 : ℝ)≤9/10 by norm_num)
    convert hlast using 1 <;> ring
  have hshort0 := hShort d H H hd hH.2
  have hshort : ((hyperbolicPrimePairPool d H (2^(128*99999*m)) H).card : ℝ) ≤
      (H : ℝ)*F*V+successorTailError m := by
    convert hshort0 using 1; dsimp [F,V,successorTailError]; norm_num; ring
  have hshortW : Real.log (X : ℝ)*
      ((hyperbolicPrimePairPool d H (2^(128*99999*m)) H).card : ℝ) ≤
        (7/100 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hshort (Real.log_natCast_nonneg X)
    rw [mul_add] at hh
    have hmain := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (H : ℝ)*F*V by positivity)
    have hid : L*V=successorShortBudget m := successorShortBudget_identity m hm1
    have he : L*((H : ℝ)*F*V)=(H : ℝ)*F*successorShortBudget m := by rw [← hid]; ring
    rw [he] at hmain
    have hmain' := hmain.trans (mul_le_mul_of_nonneg_left hSB (show 0 ≤ (H : ℝ)*F by positivity))
    have ht := hTail X H hXhi hH.1
    have h1 := mul_le_mul_of_nonneg_left hHF (show (0 : ℝ) ≤ 3/50 by norm_num)
    have h2 := div_le_div_of_nonneg_right hHX (show (0 : ℝ)≤100 by norm_num)
    simp only [div_eq_mul_inv] at hh hmain' ht h1 h2 ⊢
    nlinarith only [hh,hmain',ht,h1,h2]
  have hrough := rough_progression_card_le_long_short d (independentN 180000 m) X
    (2^(128*99999*m)) hd hds (successor_supply_smooth_cutoff_not_prime m hm1)
  rw [hY] at hrough
  have hh := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg X)
  rw [mul_add] at hh
  rw [hY]
  simp only [div_eq_mul_inv] at hh hlongW hshortW ⊢
  nlinarith only [hh,hlongW,hshortW]

end Erdos821.AnalyticSieve
