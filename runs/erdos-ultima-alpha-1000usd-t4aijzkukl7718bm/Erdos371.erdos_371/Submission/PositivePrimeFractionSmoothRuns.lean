import Submission.NarrowBandPrimeSmoothRuns

/-! A fixed positive fraction of primes have a simultaneous smooth-neighbor
run of length c*log p/(1+log log p), for some absolute c>0. This concerns a
sparse family of integers and does not settle Erdos 371. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

noncomputable def scaledPrimeRunCutoff (c : ℝ) (X : ℕ) : ℕ :=
  ⌊c*criticalPrimeRunWeight 1 X⌋₊

lemma scaledPrimeRun_data (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X ∧ 1 ≤ c*criticalPrimeRunWeight 1 X ∧
      c*criticalPrimeRunWeight 1 X ≤ Real.log X ∧ scaledPrimeRunCutoff c X ≤ X := by
  filter_upwards [criticalPrimeRun_data 1 (by norm_num),
    criticalPrimeRunWeight_dominates_logPower 1 0 (1/c) (by norm_num) (by norm_num)]
    with X hd hdom
  simp only [Real.rpow_zero,mul_one] at hdom
  have hW1 : 1 ≤ c*criticalPrimeRunWeight 1 X := by
    have hh := (div_le_iff₀ hc).mp hdom
    nlinarith
  have hWW : c*criticalPrimeRunWeight 1 X ≤ criticalPrimeRunWeight 1 X := by
    have hh := mul_le_mul_of_nonneg_right hc1 (by linarith [hd.2.1] : 0 ≤ criticalPrimeRunWeight 1 X)
    simpa only [one_mul] using hh
  exact ⟨hd.1,hW1,hWW.trans hd.2.2.1,(Nat.floor_mono hWW).trans hd.2.2.2.2⟩

lemma scaledPrimeRun_exceptional_eventual_bound (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      ((roughNeighborPrimes (scaledPrimeRunCutoff c X) X).card : ℝ)*Real.log X/X ≤
        (4*narrowLoserSieveConstant*(2*Real.log 2+1))*c +
          (16*(2 : ℝ)^65)*(Real.log X)^3/(X : ℝ)^(1/2 : ℝ) := by
  have hsmall : Tendsto (fun X : ℕ => 4*Real.log X/(X : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_rpow_div_rpow_tendsto_zero 1 1 (by norm_num)).const_mul 4
  filter_upwards [scaledPrimeRun_data c hc hc1,hsmall.eventually_le_const
    (by norm_num : (0 : ℝ) < 1),eventually_ge_atTop (2 : ℕ)] with X hd hsmall hX
  obtain ⟨hLN,hW1,hWL,hKX⟩ := hd
  let K := scaledPrimeRunCutoff c X
  let H := 2*K+1
  let W := c*criticalPrimeRunWeight 1 X
  let B : ℝ := 1+Real.log (Real.log X)
  let D : ℝ := 2*Real.log 2+1
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL0 : 0 < Real.log X := by linarith
  have hH : 0 < H := by dsimp [H]; omega
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hLL : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hLN
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hKW : (K : ℝ) ≤ W := Nat.floor_le (by linarith)
  have hHW : (H : ℝ) ≤ 4*W := by dsimp [H]; push_cast; linarith
  have hHL : (H : ℝ) ≤ 4*Real.log X := hHW.trans (by linarith)
  have hHX : H ≤ X := by
    have hh := (div_le_iff₀ hX0).mp hsmall
    have hh' : (H : ℝ) ≤ X := by linarith
    exact_mod_cast hh'
  have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  have hlogH : 1+Real.log H ≤ D*B := by
    have hh := Real.log_le_log hH0 hHL
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hL0.ne',hlog4] at hh
    dsimp [D,B]
    nlinarith [mul_nonneg h2 hLL]
  have hC : 0 ≤ narrowLoserSieveConstant := by unfold narrowLoserSieveConstant; positivity
  have hmain : narrowLoserSieveConstant*H*(1+Real.log H)/Real.log X ≤
      (4*narrowLoserSieveConstant*D)*c := by
    have hprod := mul_le_mul hHW hlogH
      (by have := Real.log_natCast_nonneg H; positivity : 0 ≤ 1+Real.log H)
      (by linarith : 0 ≤ 4*W)
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hC) hL0.le
    apply (show narrowLoserSieveConstant*H*(1+Real.log H)/Real.log X ≤
      narrowLoserSieveConstant*(4*W)*(D*B)/Real.log X by
        simpa only [mul_assoc] using hh).trans_eq
    dsimp only [W,criticalPrimeRunWeight,B]
    rw [Real.rpow_one]
    field_simp
  have herr : (2 : ℝ)^65*(H : ℝ)^2*Real.log X/(X : ℝ)^(1/2 : ℝ) ≤
      (16*(2 : ℝ)^65)*(Real.log X)^3/(X : ℝ)^(1/2 : ℝ) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg H) hHL 2
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ)^65 by positivity)) hL0.le)
      (Real.rpow_nonneg hX0.le (1/2 : ℝ))
    apply hh.trans_eq
    ring
  have hcard := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (roughNeighborPrimes_card_le_narrowLoser K X (by omega) hKX))
    hL0.le) hX0.le
  exact (hcard.trans (narrowLoserSet_scaled_log_bound X H (by omega) hHX)).trans
    (add_le_add hmain herr)

lemma scaledPrimeRunCutoff_dyadic_domination (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, X < p → p ≤ 2*X →
      scaledPrimeRunCutoff (c/2) p ≤ scaledPrimeRunCutoff c X := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually_ge_atTop 1,eventually_ge_atTop (2 : ℕ)] with X hLN hX
  intro p hpX hp2X
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hL0 : 0 < Real.log X := by linarith
  have hLX := Real.log_le_log hX0 (by exact_mod_cast hpX.le : (X : ℝ) ≤ p)
  have hlogp : Real.log p ≤ 2*Real.log X := by
    have hh := Real.log_le_log hp0 (by exact_mod_cast hp2X : (p : ℝ) ≤ 2*X)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hh
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hX : (2 : ℝ) ≤ X)
    linarith
  have hB0 : 0 < 1+Real.log (Real.log X) := by have := Real.log_nonneg hLN; positivity
  have hBB : 1+Real.log (Real.log X) ≤ 1+Real.log (Real.log p) :=
    add_le_add_right (Real.log_le_log hL0 hLX) 1
  have hW : criticalPrimeRunWeight 1 p ≤ 2*criticalPrimeRunWeight 1 X := by
    simp only [criticalPrimeRunWeight,Real.rpow_one]
    calc
      _ ≤ Real.log p/(1+Real.log (Real.log X)) :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hB0 hBB
      _ ≤ (2*Real.log X)/(1+Real.log (Real.log X)) :=
        div_le_div_of_nonneg_right hlogp hB0.le
      _ = _ := by ring
  unfold scaledPrimeRunCutoff
  apply Nat.floor_mono
  have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ c/2 by positivity)
  nlinarith

noncomputable def scaledPrimeSmoothBand (c : ℝ) (X : ℕ) : Finset ℕ :=
  (narrowPrimeBand 1 2 X).filter fun p => ∀ k ≤ scaledPrimeRunCutoff c p, 1 ≤ k →
    Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p

lemma smoothBand_complement_subset (c : ℝ) (X : ℕ)
    (hK : scaledPrimeRunCutoff c X ≤ X)
    (hdom : ∀ p : ℕ, X < p → p ≤ 2*X → scaledPrimeRunCutoff (c/2) p ≤ scaledPrimeRunCutoff c X) :
    narrowPrimeBand 1 2 X \ roughNeighborPrimes (scaledPrimeRunCutoff c X) X ⊆
      scaledPrimeSmoothBand (c/2) X := by
  intro p hp
  obtain ⟨hpband,hpnot⟩ := mem_sdiff.mp hp
  obtain ⟨_,hpX,hp2X⟩ := dyadicPrimeBand_nat_data hpband
  apply mem_filter.mpr
  refine ⟨hpband,?_⟩
  intro k hk hk1
  exact smooth_neighbors_of_not_mem_roughNeighborPrimes
    (scaledPrimeRunCutoff c X) X p hK hpband hpnot k
      (mem_Icc.mpr ⟨hk1,hk.trans (hdom p hpX hp2X)⟩)

/-- For some absolute c>0, at least half the primes in every sufficiently
large dyadic band have the full run up to floor(c*log p/(1+log log p)).
This is a prime-relative counting statement, not the Erdos 371 density. -/
theorem exists_positive_prime_fraction_log_div_loglog_smooth_runs :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (1/2 : ℝ)*(narrowPrimeBand 1 2 X).card ≤ (scaledPrimeSmoothBand c X).card := by
  let A : ℝ := 4*narrowLoserSieveConstant*(2*Real.log 2+1)
  have hA : 0 ≤ A := by
    dsimp [A,narrowLoserSieveConstant]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  let c : ℝ := 1/(16*(A+1))
  have hden : 0 < 16*(A+1) := by positivity
  have hc : 0 < c := one_div_pos.mpr hden
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hAc : A*c ≤ 1/16 := by
    dsimp only [c]
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have herr : Tendsto (fun X : ℕ =>
      (16*(2 : ℝ)^65)*(Real.log X)^3/(X : ℝ)^(1/2 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using
      (log_nat_pow_div_rpow_tendsto_zero 3 (1/2) (by norm_num)).const_mul (16*(2 : ℝ)^65)
  have hband := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hband
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [scaledPrimeRun_exceptional_eventual_bound c hc hc1,
    herr.eventually_le_const (by norm_num : (0 : ℝ) < 1/16),
    hband.eventually_const_lt (by norm_num : (1/2 : ℝ) < 1),
    scaledPrimeRun_data c hc hc1,scaledPrimeRunCutoff_dyadic_domination c hc.le,
    eventually_ge_atTop (2 : ℕ)] with X hbad herrX hbandX hd hdom hX
  let T := narrowPrimeBand 1 2 X
  let S := roughNeighborPrimes (scaledPrimeRunCutoff c X) X
  let G := scaledPrimeSmoothBand (c/2) X
  let t : ℝ := Real.log X/X
  have ht : 0 < t := div_pos (Real.log_pos (by exact_mod_cast hX))
    (by exact_mod_cast (show 0 < X by omega))
  have hb : (S.card : ℝ)*t ≤ 1/8 := by
    have hh : (S.card : ℝ)*Real.log X/X ≤ 1/8 := by
      change (S.card : ℝ)*Real.log X/X ≤ A*c+_ at hbad
      linarith
    simpa only [t,mul_div_assoc] using hh
  have hT : (1/2 : ℝ) ≤ T.card*t := by
    simpa only [T,t,mul_div_assoc] using hbandX.le
  have hScard : (S.card : ℝ) ≤ T.card/2 := by
    exact le_of_mul_le_mul_right
      (by nlinarith : (S.card : ℝ)*t ≤ (T.card/2)*t) ht
  have hGcard : ((T \ S).card : ℝ) ≤ G.card := by
    exact_mod_cast card_le_card (smoothBand_complement_subset c X hd.2.2.2 hdom)
  have hcards : (T.card : ℝ) ≤ (T \ S).card+S.card := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := T) (t := S))
  change (1/2 : ℝ)*T.card ≤ G.card
  linarith

/-- In particular there are infinitely many primes with such a run at a
fixed positive constant times the limiting scale. -/
theorem exists_infinitely_many_log_div_loglog_prime_smooth_runs :
    ∃ c : ℝ, 0 < c ∧ {p : ℕ | p.Prime ∧ ∀ k ≤ scaledPrimeRunCutoff c p, 1 ≤ k →
      Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p}.Infinite := by
  obtain ⟨c,hc,hgood⟩ := exists_positive_prime_fraction_log_div_loglog_smooth_runs
  refine ⟨c,hc,Set.infinite_of_forall_exists_gt ?_⟩
  intro M
  have hband := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hband
  obtain ⟨X,hg,hpos,hM⟩ := (hgood.and
    ((hband.eventually_const_lt (by norm_num : (0 : ℝ) < 1)).and (eventually_ge_atTop M))).exists
  have hT : 0 < (narrowPrimeBand 1 2 X).card := by
    by_contra h
    have hz : (narrowPrimeBand 1 2 X).card = 0 := by omega
    rw [hz] at hpos
    norm_num at hpos
  have hG : 0 < (scaledPrimeSmoothBand c X).card := by
    have hTr : (0 : ℝ) < (narrowPrimeBand 1 2 X).card := by exact_mod_cast hT
    have hGr : (0 : ℝ) < (scaledPrimeSmoothBand c X).card := by linarith
    exact_mod_cast hGr
  obtain ⟨p,hp⟩ := card_pos.mp hG
  obtain ⟨hpband,hrun⟩ := mem_filter.mp hp
  obtain ⟨hpprime,hpX,_⟩ := dyadicPrimeBand_nat_data hpband
  exact ⟨p,⟨hpprime,hrun⟩,by omega⟩

#print axioms scaledPrimeRun_exceptional_eventual_bound
#print axioms scaledPrimeRunCutoff_dyadic_domination
#print axioms exists_positive_prime_fraction_log_div_loglog_smooth_runs
#print axioms exists_infinitely_many_log_div_loglog_prime_smooth_runs
end Erdos371
