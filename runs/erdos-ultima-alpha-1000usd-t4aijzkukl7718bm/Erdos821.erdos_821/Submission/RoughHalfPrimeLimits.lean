import Submission.RoughHalfLimits
import Submission.WideIncidences

/-!
# Prime-only normalized incidence limits

The contribution of proper prime powers is removed with an explicit error.
The progression level remains strictly below one half.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def primePoolIncidenceMoment (D : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, ((D.filter (fun d => d ∣ p-1)).card : ℝ)*Real.log p

lemma primePoolIncidenceMoment_error (D : Finset ℕ) (N Q : ℕ)
    (hN : 1 ≤ N) (hcard : D.card ≤ Q) :
    |primePoolIncidenceMoment D N-(∑ d ∈ D, residueOneMangoldt d N)| ≤
      2*(Q : ℝ)*Real.sqrt N*Real.log N := by
  let I (n : ℕ) : ℝ := ((D.filter (fun d => d ∣ n-1)).card : ℝ)
  have hp : (Icc 1 N).filter Nat.Prime = (N+1).primesBelow := by
    ext p
    constructor
    · intro h
      obtain ⟨hI,hp⟩ := mem_filter.mp h
      exact Nat.mem_primesBelow.mpr ⟨by have := (mem_Icc.mp hI).2; omega,hp⟩
    · intro h
      obtain ⟨hN,hp⟩ := Nat.mem_primesBelow.mp h
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos,by omega⟩,hp⟩
  have hpr : (∑ n ∈ Icc 1 N with n.Prime, I n*vonMangoldt n) = primePoolIncidenceMoment D N := by
    rw [hp]
    apply sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (Nat.mem_primesBelow.mp hp).2]
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime (fun n => I n*vonMangoldt n)
  rw [hpr,← sum_family_progressions_eq_incidence] at hsplit
  have hnon : 0 ≤ ∑ n ∈ Icc 1 N with ¬n.Prime, I n*vonMangoldt n := by
    apply sum_nonneg
    intro n hn
    dsimp [I]
    positivity [vonMangoldt_nonneg (n := n)]
  have heq : primePoolIncidenceMoment D N-(∑ d ∈ D, residueOneMangoldt d N) =
      -(∑ n ∈ Icc 1 N with ¬n.Prime, I n*vonMangoldt n) := by linarith only [hsplit]
  rw [heq,abs_neg,abs_of_nonneg hnon]
  calc
    _ ≤ (Q : ℝ)*(∑ n ∈ Icc 1 N with ¬n.Prime, vonMangoldt n) := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      have hh : I n ≤ Q := by
        dsimp [I]
        exact_mod_cast (card_filter_le D (fun d => d ∣ n-1)).trans hcard
      exact mul_le_mul_of_nonneg_right hh vonMangoldt_nonneg
    _ ≤ (Q : ℝ)*(2*Real.sqrt N*Real.log N) :=
      mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) (Nat.cast_nonneg Q)
    _ = _ := by ring

lemma tendsto_div_mangoldt_of_power_saving (f : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) (C : ℝ)
    (hC : 0 ≤ C)
    (H : ∀ᶠ m : ℕ in atTop, |f m| ≤ C*(((t : ℝ)+1)*((m : ℝ)+1))^7*(2 : ℝ)^((64*t-1)*m)) :
    Tendsto (fun m => f m/mangoldtSum (progressionScaleN (t*m))) atTop (𝓝 0) := by
  have hlim := (tendsto_succ_pow_div_two_pow 7).const_mul (2*C*((t : ℝ)+1)^7)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [H,(progressionScaleN_mul_tendsto t ht).eventually eventually_mangoldt_nine_tenths]
    with m hm hpsi
  let N := progressionScaleN (t*m)
  let F : ℝ := (2 : ℝ)^((64*t-1)*m)
  let Z : ℝ := ((t : ℝ)+1)*((m : ℝ)+1)
  have hN : (0 : ℝ)<N := by dsimp [N,progressionScaleN]; positivity
  have hpsi' : (N : ℝ)/2 ≤ mangoldtSum N := by
    change (9/10 : ℝ)*(N : ℝ) ≤ mangoldtSum N at hpsi
    linarith only [hpsi,hN]
  have hpsi0 : 0 < mangoldtSum N := lt_of_lt_of_le (half_pos hN) hpsi'
  have hpow : F*(2 : ℝ)^m = (N : ℝ) := by
    simp only [F,N,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
    congr 1
    have hh := Nat.sub_add_cancel (by omega : 1 ≤ 64*t)
    nlinarith only [congrArg (fun z : ℕ => z*m) hh]
  change |f m| ≤ C*Z^7*F at hm
  change ‖f m/mangoldtSum N‖ ≤ _
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hpsi0]
  calc
    _ ≤ (C*Z^7*F)/mangoldtSum N := div_le_div_of_nonneg_right hm hpsi0.le
    _ ≤ (C*Z^7*F)/((N : ℝ)/2) :=
      div_le_div_of_nonneg_left (by dsimp [Z,F]; positivity) (half_pos hN) hpsi'
    _ = _ := by
      rw [← hpow]
      dsimp [Z]
      simp only [mul_pow]
      field_simp [show F ≠ 0 by dsimp [F]; positivity]

/-- The exact limiting mass holds for primes, not merely prime powers. -/
theorem tendsto_rough_pool_prime_normalized (D : ℕ → Finset ℕ) (a b t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hbt : 2*b+5 ≤ t)
    (hD : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, 0 < d ∧ d ≤ progressionScaleN (b*m))
    (hrough : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (a*m) ≤ c) (W : ℝ)
    (hW : Tendsto (fun m => poolTotientMass (D m)) atTop (𝓝 W)) :
    Tendsto (fun m => primePoolIncidenceMoment (D m) (progressionScaleN (t*m))/
      mangoldtSum (progressionScaleN (t*m))) atTop (𝓝 W) := by
  let E (m : ℕ) := primePoolIncidenceMoment (D m) (progressionScaleN (t*m))-
    mangoldtSum (progressionScaleN (t*m))*poolTotientMass (D m)
  have hE := tendsto_div_mangoldt_of_power_saving E t (by omega) 1000000000000000 (by norm_num) (by
    filter_upwards [eventually_ge_atTop 1] with m hm
    let N := progressionScaleN (t*m)
    let Q := progressionScaleN (b*m)
    have hcard : (D m).card ≤ Q := by
      apply (card_le_card (show D m ⊆ Icc 1 Q from fun d hd => mem_Icc.mpr (hD m hm d hd))).trans
      simp
    have hpr := primePoolIncidenceMoment_error (D m) N Q (by unfold N progressionScaleN; exact Nat.one_le_pow _ _ (by decide)) hcard
    have hmain := total_pool_progression_discrepancy (D m) N (fun d hd => (hD m hm d hd).1)
    have hh := rough_pool_below_half_combined_error (D m) a b t m ha hab ht hm hbt
      (hD m hm) (hrough m hm)
    have habs := abs_sub_le (primePoolIncidenceMoment (D m) N)
      (∑ d ∈ D m, residueOneMangoldt d N) (mangoldtSum N*poolTotientMass (D m))
    change |E m| ≤ _
    dsimp [E]
    change |primePoolIncidenceMoment (D m) N-mangoldtSum N*poolTotientMass (D m)| ≤ _
    exact habs.trans (by linarith only [hpr,hmain,hh]))
  have hsum := hE.add hW
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [(progressionScaleN_mul_tendsto t (by omega)).eventually eventually_mangoldt_nine_tenths]
    with m hm
  have hN : (0 : ℝ)<progressionScaleN (t*m) := by unfold progressionScaleN; positivity
  have hpsi : mangoldtSum (progressionScaleN (t*m)) ≠ 0 := ne_of_gt (by linarith only [hm,hN])
  dsimp [E]
  field_simp
  ring

end Erdos821
