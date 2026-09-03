import Submission.NearLinearPrimeCurrentWindows

/-! Uniform prime-weighted square bounds on fixed-ratio harmonic windows.
Every additional weight tending to zero gives convergence. The unslacked
critical energy and the sum of the signed currents are not estimated here. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def primeWindowCurrent (a N p : ℕ) : ℝ :=
  rawPrimeWinnerHarmonic p (a*N)-rawPrimeWinnerHarmonic p N

noncomputable def primeWindowMass (a N p : ℕ) : ℝ :=
  ∑ n ∈ (Ico N (a*N)).filter (fun n => primeWinner n=p), (1 : ℝ)/n

lemma primeWindowMass_nonneg (a N p : ℕ) : 0≤primeWindowMass a N p := by
  unfold primeWindowMass
  positivity

lemma primeWindowCurrent_abs_le_mass (a N p : ℕ) (ha : 1≤a) :
    |primeWindowCurrent a N p|≤primeWindowMass a N p := by
  have hNU : N≤a*N := by nlinarith
  unfold primeWindowCurrent rawPrimeWinnerHarmonic
  rw [← sum_Ico_eq_sub _ hNU]
  have h := norm_sum_le (Ico N (a*N)) (primeWinnerHarmonicTerm p)
  rw [← Real.norm_eq_abs]
  simpa only [primeWindowMass,sum_filter,primeWinnerHarmonicTerm,apply_ite,
    norm_div,factorSign_norm,Real.norm_natCast,norm_zero] using h

lemma primeWinner_window_card_bound (L U p : ℕ) (hL : 0<L) :
    ((Ico L U).filter (fun n => primeWinner n=p)).card ≤ 2*(U/p) := by
  let S := (range (U+1)).filter fun n => n≠0 ∧ p ∣ n
  let T := (range U).filter fun n => p ∣ n+1
  have hs : (Ico L U).filter (fun n => primeWinner n=p) ⊆ S ∪ T := by
    intro n hn
    obtain ⟨hn,he⟩ := mem_filter.mp hn
    obtain ⟨hnL,hnU⟩ := mem_Ico.mp hn
    have hcase : Nat.maxPrimeFac n=p ∨ Nat.maxPrimeFac (n+1)=p := by
      rcases max_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h|h
      · exact Or.inl (h.1.symm.trans he)
      · exact Or.inr (h.1.symm.trans he)
    rcases hcase with h|h
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,by
        rw [← h]; exact Nat.maxPrimeFac_dvd⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨mem_range.mpr hnU,by
        rw [← h]; exact Nat.maxPrimeFac_dvd⟩
  have hh := (card_le_card hs).trans (card_union_le S T)
  simpa only [S,T,Nat.card_multiples',Nat.card_multiples,two_mul] using hh

/-- The harmonic incidence mass in [N,aN) is at most 2a/p.
This uses spacing, not cancellation among the signs. -/
lemma primeWindowMass_mul_label_bound (a N p : ℕ) (hN : 0<N) :
    (p : ℝ)*primeWindowMass a N p≤2*a := by
  let S := (Ico N (a*N)).filter fun n => primeWinner n=p
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hb : primeWindowMass a N p≤(S.card : ℝ)/N := by
    unfold primeWindowMass
    calc
      _ ≤ ∑ _n ∈ S, (1 : ℝ)/N := by
        apply sum_le_sum
        intro n hn
        apply one_div_le_one_div_of_le hNr
        exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
      _ = _ := by simp only [sum_const,nsmul_eq_mul,mul_one_div]
  have hc : p*S.card≤2*(a*N) := by
    have h := primeWinner_window_card_bound N (a*N) p hN
    have hd := Nat.mul_div_le (a*N) p
    dsimp only [S]
    nlinarith
  have hcr : (p : ℝ)*S.card≤2*((a*N : ℕ) : ℝ) := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) p)
  calc
    _ ≤ (p : ℝ)*((S.card : ℝ)/N) := hm
    _ = ((p : ℝ)*S.card)/N := by ring
    _ ≤ (2*((a*N : ℕ) : ℝ))/N := div_le_div_of_nonneg_right hcr hNr.le
    _ = 2*a := by push_cast; field_simp

lemma primeWindowMass_sum_bound (a N : ℕ) (P : Finset ℕ) (hN : 0<N) :
    (∑ p ∈ P, primeWindowMass a N p)≤a := by
  classical
  let S := (Ico N (a*N)).filter fun n => primeWinner n∈P
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  calc
    _ = ∑ n ∈ S, (1 : ℝ)/n := sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ _n ∈ S, (1 : ℝ)/N := by
      apply sum_le_sum
      intro n hn
      apply one_div_le_one_div_of_le hNr
      exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
    _ = (S.card : ℝ)/N := by simp only [sum_const,nsmul_eq_mul,mul_one_div]
    _ ≤ ((a*N : ℕ) : ℝ)/N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      exact_mod_cast (card_le_card (show S ⊆ range (a*N) from
        fun n hn => mem_range.mpr (mem_Ico.mp (mem_filter.mp hn).1).2)).trans_eq (card_range _)
    _ = a := by push_cast; field_simp

/-- The critical weighted energy is bounded uniformly in N and the finite
set of prime labels. Boundedness is not convergence to zero. -/
theorem primeWindow_critical_energy_bound (a N : ℕ) (P : Finset ℕ) (ha : 1≤a) :
    (∑ p ∈ P, (p : ℝ)*(primeWindowCurrent a N p)^2)≤2*(a : ℝ)^2 := by
  by_cases hN : N=0
  · subst N
    simp [primeWindowCurrent]
  have hNp : 0<N := Nat.pos_of_ne_zero hN
  have hterm (p : ℕ) (_hp : p∈P) :
      (p : ℝ)*(primeWindowCurrent a N p)^2≤2*a*primeWindowMass a N p := by
    have hm := primeWindowCurrent_abs_le_mass a N p ha
    have hd := primeWindowMass_mul_label_bound a N p hNp
    have hsq := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hm 2) (Nat.cast_nonneg (α := ℝ) p)
    rw [sq_abs] at hsq
    have hh := mul_le_mul_of_nonneg_right hd (primeWindowMass_nonneg a N p)
    nlinarith
  calc
    _ ≤ ∑ p ∈ P, 2*a*primeWindowMass a N p := sum_le_sum hterm
    _ = 2*a*∑ p ∈ P, primeWindowMass a N p := (mul_sum ..).symm
    _ ≤ 2*a*(a : ℝ) := mul_le_mul_of_nonneg_left
      (primeWindowMass_sum_bound a N P hNp) (by positivity)
    _ = _ := by ring

lemma primeWindowCurrent_fixed_label_zero (a p : ℕ) (ha : 1≤a) :
    Tendsto (fun N => primeWindowCurrent a N p) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => a*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; nlinarith) tendsto_id
  simpa only [primeWindowCurrent,Function.comp_apply,sub_self] using
    ((rawPrimeWinnerHarmonic_tendsto p).comp ht).sub (rawPrimeWinnerHarmonic_tendsto p)

noncomputable def primeWindowWeightedEnergy (w : ℕ → ℝ) (a N : ℕ) : ℝ :=
  ∑ p ∈ range (a*N+1), w p*(p : ℝ)*(primeWindowCurrent a N p)^2

/-- Any nonnegative extra weight tending to zero makes the critical square
energy tend to zero, however slowly that extra weight decays. This does NOT
allow the weight to be identically one. -/
theorem primeWindow_weighted_energy_zero (w : ℕ → ℝ) (hw : ∀ p, 0≤w p)
    (hw0 : Tendsto w atTop (𝓝 0)) (a : ℕ) (ha : 1≤a) :
    Tendsto (primeWindowWeightedEnergy w a) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(4*(a : ℝ)^2+1)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨B,hB⟩ := eventually_atTop.mp (hw0.eventually_lt_const hη)
  have hhead : Tendsto (fun N => ∑ p ∈ range B,
      w p*(p : ℝ)*(primeWindowCurrent a N p)^2) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (range B) (fun p _ =>
      ((primeWindowCurrent_fixed_label_zero a p ha).pow 2).const_mul (w p*(p : ℝ)))
    simpa only [zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,sum_const_zero] using h
  filter_upwards [hhead.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity)] with N hsmall
  have hnon : 0≤primeWindowWeightedEnergy w a N := by
    unfold primeWindowWeightedEnergy
    exact sum_nonneg (fun p _ => mul_nonneg (mul_nonneg (hw p) (Nat.cast_nonneg p)) (sq_nonneg _))
  have hrow (p : ℕ) (_hp : p∈range (a*N+1)) :
      w p*(p : ℝ)*(primeWindowCurrent a N p)^2 ≤
        (if p<B then w p*(p : ℝ)*(primeWindowCurrent a N p)^2 else 0)+
          η*((p : ℝ)*(primeWindowCurrent a N p)^2) := by
    by_cases hpB : p<B
    · rw [if_pos hpB]
      exact le_add_of_nonneg_right (by positivity)
    · rw [if_neg hpB,zero_add]
      have h := mul_le_mul_of_nonneg_right (hB p (by omega)).le
        (show 0≤(p : ℝ)*(primeWindowCurrent a N p)^2 by positivity)
      simpa only [mul_assoc] using h
  have hs := sum_le_sum hrow
  rw [sum_add_distrib,← mul_sum] at hs
  have hh : (∑ p ∈ range (a*N+1), if p<B then
      w p*(p : ℝ)*(primeWindowCurrent a N p)^2 else 0) ≤
        ∑ p ∈ range B, w p*(p : ℝ)*(primeWindowCurrent a N p)^2 := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_range.mpr (mem_filter.mp hp).2
    · intro p _ _
      exact mul_nonneg (mul_nonneg (hw p) (Nat.cast_nonneg p)) (sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_left
    (primeWindow_critical_energy_bound a N (range (a*N+1)) ha) hη.le
  have hηbound : η*(2*(a : ℝ)^2)<ε/2 := by
    dsimp [η]
    have hd : (0 : ℝ)<4*(a : ℝ)^2+1 := by positivity
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    field_simp
    nlinarith [sq_nonneg (a : ℝ)]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnon]
  change (∑ p ∈ range (a*N+1), w p*(p : ℝ)*(primeWindowCurrent a N p)^2)<ε
  linarith

/-- The coordinate bound has no logarithmic loss on a fixed-ratio window. -/
lemma primeWindowCurrent_reciprocal_bound (a N p : ℕ) (ha : 1≤a) (hp : 0<p) :
    |primeWindowCurrent a N p|≤2*(a : ℝ)/p := by
  by_cases hN : N=0
  · subst N
    simp only [primeWindowCurrent,mul_zero,sub_self,abs_zero]
    positivity
  have hd := primeWindowMass_mul_label_bound a N p (Nat.pos_of_ne_zero hN)
  have hm := mul_le_mul_of_nonneg_left (primeWindowCurrent_abs_le_mass a N p ha)
    (Nat.cast_nonneg (α := ℝ) p)
  apply (le_div_iff₀ (by exact_mod_cast hp : (0 : ℝ)<p)).mpr
  nlinarith

lemma primeWindowWeightedEnergy_eq_tsum (w : ℕ → ℝ) (a N : ℕ) (ha : 1≤a) :
    primeWindowWeightedEnergy w a N =
      ∑' p : ℕ, w p*(p : ℝ)*(primeWindowCurrent a N p)^2 := by
  classical
  symm
  apply tsum_eq_sum
  intro p hp
  have hpU : a*N<p := by simp only [mem_range,not_lt] at hp; omega
  have hNU : N≤a*N := by nlinarith
  rw [primeWindowCurrent,
    rawPrimeWinnerHarmonic_zero_above_endpoint p (a*N) hpU,
    rawPrimeWinnerHarmonic_zero_above_endpoint p N (hNU.trans_lt hpU),
    sub_self,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero]

/-- The same convergence statement for the full infinite prime-indexed
vector, not merely for a fixed finite selection of labels. -/
theorem primeWindow_weighted_energy_tsum_zero (w : ℕ → ℝ) (hw : ∀ p, 0≤w p)
    (hw0 : Tendsto w atTop (𝓝 0)) (a : ℕ) (ha : 1≤a) :
    Tendsto (fun N => ∑' p : ℕ, w p*(p : ℝ)*(primeWindowCurrent a N p)^2)
      atTop (𝓝 0) := by
  simpa only [← primeWindowWeightedEnergy_eq_tsum w a _ ha] using
    primeWindow_weighted_energy_zero w hw hw0 a ha

/-- In particular, any positive logarithmic slack suffices. The endpoint
exponent delta=0 is deliberately excluded. -/
theorem primeWindow_log_slack_energy_zero (δ : ℝ) (hδ : 0<δ) (a : ℕ) (ha : 1≤a) :
    Tendsto (primeWindowWeightedEnergy
      (fun p => (1+Real.log (p+1 : ℝ))^(-δ)) a) atTop (𝓝 0) := by
  have hlog : Tendsto (fun p : ℕ => Real.log (p+1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))
  have hbase : Tendsto (fun p : ℕ => 1+Real.log (p+1 : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop hlog
  apply primeWindow_weighted_energy_zero _ _
    ((tendsto_rpow_neg_atTop hδ).comp hbase) a ha
  intro p
  apply Real.rpow_nonneg
  have h := Real.log_nonneg (show (1 : ℝ)≤p+1 by have := Nat.cast_nonneg (α := ℝ) p; linarith)
  linarith

#print axioms primeWindowCurrent_reciprocal_bound
#print axioms primeWindow_weighted_energy_tsum_zero
#print axioms primeWindow_log_slack_energy_zero

#print axioms primeWindow_critical_energy_bound
#print axioms primeWindow_weighted_energy_zero
end Erdos371
