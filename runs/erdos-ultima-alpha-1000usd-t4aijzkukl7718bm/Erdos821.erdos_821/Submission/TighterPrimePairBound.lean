import Submission.UncappedEndpoint

/-!
# A longer prime-pair sieve within the existing error budget

The sieve length is 2^floor(639*J/20). Its 2+1/1000 error exponent
still fits below 2^(64*J), while the squared logarithmic denominator
improves from 900*J^2 to 1020*J^2.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821
set_option maxHeartbeats 3000000
namespace Sieve

lemma tight_pair_length_bounds (J : ℕ) (hJ : 100 ≤ J) :
    0 < 639*J/20 ∧ 1597*J ≤ 50*(639*J/20) ∧
      2001*(639*J/20) ≤ 1000*(64*J-1) ∧ 639*J/20 ≤ 64*J-1 := by
  omega

lemma tight_pair_log_square (J : ℕ) (hJ : 100 ≤ J) :
    (1020 : ℝ)*((J : ℝ)*Real.log 2)^2 ≤
      ((639*J/20 : ℕ)*Real.log 2)^2 := by
  have hlen : (1597 : ℝ)*J ≤ 50*((639*J/20 : ℕ) : ℝ) := by
    exact_mod_cast (tight_pair_length_bounds J hJ).2.1
  have hratio : (1597/50 : ℝ)*J ≤ ((639*J/20 : ℕ) : ℝ) := by linarith
  have hs := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (1597/50 : ℝ)*J)
    (Nat.cast_nonneg (639*J/20)) |>.mpr hratio
  have hsq : (1020 : ℝ)*(J : ℝ)^2 ≤ ((639*J/20 : ℕ) : ℝ)^2 := by
    nlinarith [sq_nonneg (J : ℝ)]
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log 2))
  nlinarith only [hh]

theorem eventually_prime_pair_tight_explicit_all :
    ∀ᶠ J : ℕ in atTop, ∀ N a : ℕ, 0 < a →
      (((range N).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card : ℝ) ≤
        2*(N : ℝ)/(1020*((a.totient : ℝ)/a*((J : ℝ)*Real.log 2)^2))+
          (2 : ℝ)^(64*J)+1 := by
  have ht : Tendsto (fun J : ℕ => 2^(639*J/20)) atTop atTop := by
    apply tendsto_atTop_mono (fun J => ?_) tendsto_id
    exact (Nat.lt_two_pow_self (n := J)).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  filter_upwards [ht.eventually (eventually_mixed_prime_pair_sieve_bound (1/1000) (by norm_num)),
    eventually_ge_atTop 100] with J hpair hJ
  intro N a ha
  by_cases h2a : 2 ∣ a
  · let L := 639*J/20
    let z := 2^L
    let P := (z+1).primesBelow
    let G := mixedPairDenominator a z P
    let B : ℝ := (a.totient : ℝ)/a*((L : ℝ)*Real.log 2)^2
    have hL : 0 < L := (tight_pair_length_bounds J hJ).1
    have hB : 0 < B := by
      dsimp [B]
      exact mul_pos (div_pos (by exact_mod_cast Nat.totient_pos.mpr ha) (by positivity))
        (sq_pos_of_pos (mul_pos (by exact_mod_cast hL) (Real.log_pos (by norm_num))))
    have hG : B/2 ≤ G := mixedPairDenominator_dyadic_lower a L ha h2a
    have hGpos : 0 < G := (div_pos hB (by norm_num)).trans_le hG
    have hinv : G⁻¹ ≤ 2/B := by
      rw [← inv_div]
      exact (inv_le_inv₀ hGpos (div_pos hB (by norm_num))).mpr hG
    have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ z := by
      obtain ⟨hpz,hpr⟩ := Nat.mem_primesBelow.mp hp
      exact ⟨hpr,by omega⟩
    have hb := hpair N a h2a P hP
    let T := (range N).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧ z < q ∧ z < a*q+1)
    let S := (range N).filter (fun q => q.Prime ∧ (a*q+1).Prime)
    have hT : (T.card : ℝ) ≤ 2*(N : ℝ)/B+(z : ℝ)^(2+1/1000 : ℝ) := by
      calc
        _ ≤ (N : ℝ)*G⁻¹+(z : ℝ)^(2+1/1000 : ℝ) := hb
        _ ≤ (N : ℝ)*(2/B)+(z : ℝ)^(2+1/1000 : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)) le_rfl
        _ = _ := by ring
    have hsub : S ⊆ T ∪ range (z+1) := by
      intro q hq
      obtain ⟨hqN,hqp,haqp⟩ := mem_filter.mp hq
      by_cases hzq : z < q
      · apply mem_union_left
        have hqaq := Nat.le_mul_of_pos_left q ha
        exact mem_filter.mpr ⟨hqN,hqp,haqp,hzq,by omega⟩
      · exact mem_union_right _ (mem_range.mpr (by omega))
    have hcard : (S.card : ℝ) ≤ (T.card : ℝ)+(z : ℝ)+1 := by
      have hc : S.card ≤ T.card+(z+1) := by
        simpa only [card_range] using (card_le_card hsub).trans (card_union_le _ _)
      exact_mod_cast hc
    have hpow : (z : ℝ)^(2+1/1000 : ℝ) ≤ (2 : ℝ)^(64*J-1) := by
      dsimp [z]
      rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast_mul (by norm_num),← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h := (tight_pair_length_bounds J hJ).2.2.1
      have hh : (2001 : ℝ)*L ≤ 1000*((64*J-1 : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hzle : (z : ℝ) ≤ (2 : ℝ)^(64*J-1) := by
      dsimp [z]
      rw [Nat.cast_pow,Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) (tight_pair_length_bounds J hJ).2.2.2
    have herr : (z : ℝ)^(2+1/1000 : ℝ)+(z : ℝ) ≤ (2 : ℝ)^(64*J) := by
      calc
        _ ≤ (2 : ℝ)^(64*J-1)+(2 : ℝ)^(64*J-1) := add_le_add hpow hzle
        _ = (2 : ℝ)^(64*J-1+1) := by rw [_root_.pow_succ]; ring
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 64*J)]
    have hBnew : 1020*((a.totient : ℝ)/a*((J : ℝ)*Real.log 2)^2) ≤ B := by
      have h := mul_le_mul_of_nonneg_left (tight_pair_log_square J hJ)
        (show (0 : ℝ) ≤ (a.totient : ℝ)/a by positivity)
      convert h using 1; dsimp [B,L]; ring
    have hdenpos : 0 < 1020*((a.totient : ℝ)/a*((J : ℝ)*Real.log 2)^2) := by
      have hjR : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
      have hphi : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
      positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hmain := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2*(N : ℝ)) hdenpos hBnew
    change (S.card : ℝ) ≤ _
    linarith only [hT,hcard,herr,hmain]
  · have hh : (((range N).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card : ℝ) ≤ 1 := by
      exact_mod_cast prime_pair_odd_card_le_one N a ha h2a
    have hmain : 0 ≤ 2*(N : ℝ)/(1020*((a.totient : ℝ)/a*((J : ℝ)*Real.log 2)^2)) := by positivity
    have herr : 0 ≤ (2 : ℝ)^(64*J) := by positivity
    linarith

end Sieve
namespace AnalyticSieve

def TightEndpointPairUpTo (X J : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → a ≤ X →
    (primePairCofactorCount X a : ℝ) ≤
      (X : ℝ)/(510*(a.totient : ℝ)*((J : ℝ)*Real.log 2)^2)+
        ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1)

theorem eventually_tight_endpoint_pair_ambient (t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ, m ≤ J → ∀ X : ℕ,
      X ≤ independentN t m → TightEndpointPairUpTo X J := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp Sieve.eventually_prime_pair_tight_explicit_all
  filter_upwards [eventually_totient_ratio_ambient_scale t ht,eventually_ge_atTop (max 1 L)]
    with m hratio hm
  intro J hmJ X hXN a ha haX
  have hJ : 1 ≤ J := by omega
  have hpair := hL J (by omega)
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  have hJlog : (1/2 : ℝ) ≤ (J : ℝ)*Real.log 2 := by
    have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hD : 1 ≤ 510*D := by
    dsimp [D]
    nlinarith [sq_nonneg ((J : ℝ)*Real.log 2-1/2)]
  have hD0 : 0 < D := by nlinarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hphi : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hN : ((X/a+1 : ℕ) : ℝ) ≤ (X : ℝ)/a+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using add_le_add Nat.cast_div_le (le_refl (1 : ℝ))
  have hb := hpair (X/a+1) a ha
  have hcorr : (a : ℝ)/(510*(a.totient : ℝ)*D) ≤ (2 : ℝ)^(16*J) := by
    calc
      _ = ((a : ℝ)/(a.totient : ℝ))/(510*D) := by ring
      _ ≤ (a : ℝ)/(a.totient : ℝ) := div_le_self (by positivity) hD
      _ ≤ (2 : ℝ)^m := hratio a ha (haX.trans hXN)
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmain : 2*((X/a+1 : ℕ) : ℝ)/(1020*((a.totient : ℝ)/a*D)) ≤
      (X : ℝ)/(510*(a.totient : ℝ)*D)+(2 : ℝ)^(16*J) := by
    calc
      _ ≤ 2*((X : ℝ)/a+1)/(1020*((a.totient : ℝ)/a*D)) := by gcongr
      _ = (X : ℝ)/(510*(a.totient : ℝ)*D)+(a : ℝ)/(510*(a.totient : ℝ)*D) := by
        field_simp
        ring
      _ ≤ _ := add_le_add le_rfl hcorr
  change (primePairCofactorCount X a : ℝ) ≤ _ at hb
  change (primePairCofactorCount X a : ℝ) ≤ (X : ℝ)/(510*(a.totient : ℝ)*D)+_
  linarith only [hb,hmain]

end AnalyticSieve
end Erdos821
