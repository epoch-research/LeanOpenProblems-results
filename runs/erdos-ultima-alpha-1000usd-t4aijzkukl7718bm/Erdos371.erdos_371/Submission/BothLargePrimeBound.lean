import Submission.SelbergCofactorPairs

/-! A quadratic upper bound for simultaneous very large prime factors of
consecutive integers. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

noncomputable def bothLargePrimeSet (N : ℕ) (u : ℝ) : Finset ℕ :=
  (range N).filter (fun n => (N : ℝ)^(1-u) < (Nat.maxPrimeFac n : ℝ) ∧
    (N : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ))

noncomputable def largePairConstant : ℝ := 4*Real.exp 19*256^2

lemma primeCofactor_le_power_cutoff (N n : ℕ) (hN : 0 < N) (hn : n ≤ N) (u : ℝ)
    (hp : (N : ℝ)^(1-u) ≤ Nat.maxPrimeFac n) :
    (primeCofactor n : ℝ) ≤ (N : ℝ)^u := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : 0 < (N : ℝ)^(1-u) := Real.rpow_pos_of_pos hn0 _
  have he : (Nat.maxPrimeFac n : ℝ)*primeCofactor n = n := by exact_mod_cast maxPrimeFac_mul_primeCofactor n
  have ha : 0 ≤ (primeCofactor n : ℝ) := Nat.cast_nonneg _
  have hnl : (n : ℝ) ≤ N := by exact_mod_cast hn
  have h : (primeCofactor n : ℝ) ≤ N/(N : ℝ)^(1-u) :=
    (le_div_iff₀ hpow).mpr (by nlinarith)
  have hpow' : (N : ℝ)/(N : ℝ)^(1-u)=(N : ℝ)^u := by
    calc
      _ = (N : ℝ)^(1 : ℝ)/(N : ℝ)^(1-u) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hn0]; congr 1; ring
  rwa [hpow'] at h

lemma bothLargePrimeSet_subset_cofactors (N : ℕ) (u : ℝ)
    (hN : 1 < N) (hu0 : 0 ≤ u) (hu : u ≤ 1/8) :
    bothLargePrimeSet N u ⊆ allCofactorPrimeSet N ⌊(N : ℝ)^u⌋₊ ⌊(N : ℝ)^(1/256 : ℝ)⌋₊ := by
  intro n hn
  obtain ⟨hnN,hp,hq⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlarge : (1 : ℝ) < (N : ℝ)^(1-u) := Real.one_lt_rpow hn1 (by linarith)
  have hn2 : 1 < n := by
    apply (Nat.one_lt_maxPrimeFac_iff n).mp
    exact_mod_cast hlarge.trans hp
  have hA := primeCofactor_le_power_cutoff N n (by omega) (by omega) u hp.le
  have hB := primeCofactor_le_power_cutoff N (n+1) (by omega) (by omega) u hq.le
  have hAX : primeCofactor n ≤ ⌊(N : ℝ)^u⌋₊ := (Nat.le_floor_iff (Real.rpow_nonneg hn0.le u)).mpr hA
  have hBX : primeCofactor (n+1) ≤ ⌊(N : ℝ)^u⌋₊ := (Nat.le_floor_iff (Real.rpow_nonneg hn0.le u)).mpr hB
  obtain ⟨ha0,had,hpa⟩ := primeCofactor_data n hn2
  obtain ⟨hb0,hbd,hqb⟩ := primeCofactor_data (n+1) (by omega)
  have hzlt : (⌊(N : ℝ)^(1/256 : ℝ)⌋₊ : ℝ) < (N : ℝ)^(1-u) :=
    (Nat.floor_le (Real.rpow_nonneg hn0.le _)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith))
  apply mem_biUnion.mpr
  refine ⟨primeCofactor n,mem_Icc.mpr ⟨ha0,hAX⟩,?_⟩
  apply mem_biUnion.mpr
  refine ⟨primeCofactor (n+1),mem_Icc.mpr ⟨hb0,hBX⟩,?_⟩
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨by omega,by omega⟩,had,hbd,?_⟩
  rw [hpa,hqb]
  exact ⟨Nat.prime_maxPrimeFac_of_one_lt n hn2,Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),
    by exact_mod_cast hzlt.trans hp,by exact_mod_cast hzlt.trans hq⟩

lemma bothLargePrimeSet_ratio_bound (N : ℕ) (u : ℝ) (hN : 1 < N)
    (hu0 : 0 ≤ u) (hu : u ≤ 1/8) :
    ((bothLargePrimeSet N u).card : ℝ)/N ≤
      largePairConstant*(u+1/Real.log N)^2 + (2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ) := by
  let X := ⌊(N : ℝ)^u⌋₊
  let z := ⌊(N : ℝ)^(1/256 : ℝ)⌋₊
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hXpos : 1 ≤ X := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hu0)
  have hzpos : 1 ≤ z := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 (by norm_num))
  have hX : (X : ℝ) ≤ (N : ℝ)^u := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hXsq : (X : ℝ)^2 ≤ (N : ℝ)^(1/4 : ℝ) := by
    calc
      _ ≤ ((N : ℝ)^u)^2 := pow_le_pow_left₀ (Nat.cast_nonneg X) hX 2
      _ = (N : ℝ)^(u*2) := by rw [Real.rpow_mul hn0.le,Real.rpow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hXN : X^2 ≤ N := by
    have h := hXsq.trans (show (N : ℝ)^(1/4 : ℝ) ≤ N from by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/4 : ℝ) ≤ 1))
    exact_mod_cast h
  have hzupper : (z+1 : ℝ) ≤ 2*(N : ℝ)^(1/256 : ℝ) := by
    have hz := Nat.floor_le (Real.rpow_nonneg hn0.le (1/256 : ℝ))
    have hz1 := Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/256)
    dsimp only [z]
    linarith
  have hlogz : Real.log N/256 ≤ Real.log (z+1 : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn0 (1/256 : ℝ))
      (Nat.lt_floor_add_one ((N : ℝ)^(1/256 : ℝ))).le
    rw [Real.log_rpow hn0] at h
    convert h using 1 <;> ring
  have hlogzpos : 0 < Real.log (z+1 : ℝ) := lt_of_lt_of_le (by positivity) hlogz
  have hlogX : Real.log X ≤ u*Real.log N := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < X by omega) : (0 : ℝ) < X) hX
    rwa [Real.log_rpow hn0] at h
  have hratio : (1+Real.log X)/Real.log (z+1 : ℝ) ≤ 256*(u+1/Real.log N) := by
    calc
      _ ≤ (1+u*Real.log N)/Real.log (z+1 : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hlogzpos.le
      _ ≤ (1+u*Real.log N)/(Real.log N/256) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlogz
      _ = _ := by field_simp; ring
  have hmain : 4*Real.exp 19*(1+Real.log X)^2/(Real.log (z+1 : ℝ))^2 ≤
      largePairConstant*(u+1/Real.log N)^2 := by
    have hsq := pow_le_pow_left₀ (div_nonneg (by have := Real.log_natCast_nonneg X; positivity) hlogzpos.le) hratio 2
    have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*Real.exp 19 by positivity)
    dsimp only [largePairConstant]
    convert h using 1 <;> ring
  have hzpow : (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*(N : ℝ)^(1/4 : ℝ) := by
    calc
      _ ≤ (2*(N : ℝ)^(1/256 : ℝ))^64 := pow_le_pow_left₀ (by positivity) hzupper 64
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
        norm_num
  have herr : 2*(X : ℝ)^2*(z+1 : ℝ)^64/N ≤ (2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ) := by
    calc
      _ ≤ 2*(N : ℝ)^(1/4 : ℝ)*((2 : ℝ)^64*(N : ℝ)^(1/4 : ℝ))/N := by
        apply div_le_div_of_nonneg_right _ hn0.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hXsq (by norm_num)) hzpow (by positivity) (by positivity)
      _ = _ := by
        have he : (N : ℝ)^(1/4 : ℝ)*(N : ℝ)^(1/4 : ℝ)/N=(N : ℝ)^(-1/2 : ℝ) := by
          rw [← Real.rpow_add hn0]
          calc
            _ = (N : ℝ)^(1/2 : ℝ)/(N : ℝ)^(1 : ℝ) := by norm_num
            _ = _ := by rw [← Real.rpow_sub hn0]; norm_num
        calc
          _ = (2 : ℝ)^65*((N : ℝ)^(1/4 : ℝ)*(N : ℝ)^(1/4 : ℝ)/N) := by ring
          _ = _ := by rw [he]
  have hcard := (Nat.cast_le (α := ℝ)).mpr (card_le_card (bothLargePrimeSet_subset_cofactors N u hN hu0 hu))
  have hb := hcard.trans (allCofactorPrimeSet_bound N X z hzpos hXN)
  have hb' := div_le_div_of_nonneg_right hb hn0.le
  have he : (4*Real.exp 19*N*(1+Real.log X)^2/(Real.log (z+1 : ℝ))^2 +
      2*(X : ℝ)^2*(z+1 : ℝ)^64)/N =
      4*Real.exp 19*(1+Real.log X)^2/(Real.log (z+1 : ℝ))^2 +
      2*(X : ℝ)^2*(z+1 : ℝ)^64/N := by field_simp
  rw [he] at hb'
  exact hb'.trans (add_le_add hmain herr)

/-- Simultaneous prime factors above `N^(1-u)` have upper density bounded
quadratically in the small parameter `u`. -/
theorem bothLargePrimeSet_eventually_ratio_le (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/8)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((bothLargePrimeSet N u).card : ℝ)/N ≤ largePairConstant*u^2+ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hlog
  have hmain := ((hi.const_add u).pow 2).const_mul largePairConstant
  have herr := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
    tendsto_natCast_atTop_atTop).const_mul ((2 : ℝ)^65)
  have ht := hmain.add herr
  simp only [add_zero,mul_zero,Function.comp_def] at ht
  filter_upwards [ht.eventually_lt_const (show largePairConstant*u^2 < largePairConstant*u^2+ε by linarith),
    eventually_gt_atTop (1 : ℕ)] with N hN hN1
  have hb := bothLargePrimeSet_ratio_bound N u hN1 hu0 hu
  simp only [one_div,neg_div] at hb hN
  exact hb.trans hN.le

#print axioms bothLargePrimeSet_ratio_bound
#print axioms bothLargePrimeSet_eventually_ratio_le
end FiniteSieve
end Erdos371
