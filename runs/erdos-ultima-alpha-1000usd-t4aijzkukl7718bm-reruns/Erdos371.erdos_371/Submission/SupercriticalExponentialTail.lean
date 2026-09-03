import FormalConjecturesUtil
import Submission.SupercriticalUniformTail
import Submission.PrimeDivisorExponentialMoment

/-! Exponential tails for the supercritical-pair multiplicity. This is an
unsigned estimate and does not prove the original density conjecture. -/

namespace Erdos371SupercriticalExponentialTail

open Finset Filter Erdos371PrimeDiscrepancy Erdos371SupercriticalPrimePairs
open Erdos371SupercriticalMultiplicityTail Erdos371SupercriticalUniformTail
open Erdos371PrimeLogBands Erdos371PrimeDivisorSecondMoment
open Erdos371SmallPrimeAveraging Erdos371PrimeDivisorExponentialMoment

lemma factorNeighbors_exp_bound {s : Finset ℕ} (hs : ∀ p∈s,p.Prime) {k : ℕ}
    (hM : mass s ≤ 8*(k+1:ℕ)) (N : ℕ) :
    ((factorNeighbors s (32*(k+1)) N).card:ℝ) ≤ 2*(N:ℝ)/(2:ℝ)^(2*k) := by
  have hc : ((factorNeighbors s (32*(k+1)) N).card:ℝ) ≤
      2*(badFactors s (32*(k+1)) N).card := by
    exact_mod_cast factorNeighbors_card s (32*(k+1)) N
  calc
    _ ≤ _ := hc
    _ ≤ 2*((N:ℝ)/(2:ℝ)^(2*k)) :=
      mul_le_mul_of_nonneg_left (linear_threshold_bound s hs hM N) (by norm_num)
    _ = _ := by ring

lemma global_exp_tail {k T : ℕ} (hT : T<2^(2*k)) :
    (tailCount (32*(k+1)) (2^T):ℝ) ≤ 2*(2:ℝ)^T/(2:ℝ)^(2*k) := by
  have hM : mass (band 1 (T+1)) ≤ 8*(k+1:ℕ) := by
    have hh := band_mass_bound (L := 1) (U := T+1) (B := 2*k) (by omega)
      (by simpa using hT)
    change mass (band 1 (T+1)) ≤ 4*(2*k:ℕ) at hh
    push_cast at hh ⊢
    linarith
  have hsub : (range (2^T)).filter (fun n => 32*(k+1) ≤ Erdos371SupercriticalPrimePairs.multiplicity n) ⊆
      factorNeighbors (band 1 (T+1)) (32*(k+1)) (2^T) := by
    intro n hn
    obtain ⟨hn,hm⟩ := mem_filter.mp hn
    exact mem_factorNeighbors (by positivity) (mem_range.mp hn) hm
      (fun q hq hqN _ => prime_band_cover hq hqN)
  have hh : (tailCount (32*(k+1)) (2^T):ℝ) ≤
      (factorNeighbors (band 1 (T+1)) (32*(k+1)) (2^T)).card := by
    exact_mod_cast card_le_card hsub
  exact hh.trans (by simpa using factorNeighbors_exp_bound (fun p hp => band_primes hp) hM (2^T))

/-- The threshold is now linear in `k`, while the tail decays geometrically. -/
theorem dyadic_exp_tail {k : ℕ} (hk : 2 ≤ k) (T : ℕ) :
    (tailCount (32*(k+1)) (2^T):ℝ) ≤ 64*(2:ℝ)^T*(k+1:ℕ)/(2:ℝ)^(2*k) := by
  by_cases hT : T<2^(2*k)
  · have hh := global_exp_tail (k := k) hT
    apply hh.trans
    have hkn : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
    have hc : (2:ℝ) ≤ 64*(k+1:ℕ) := by linarith
    calc
      _ ≤ (64*(k+1:ℕ))*((2:ℝ)^T)/(2:ℝ)^(2*k) := by gcongr
      _ = _ := by ring
  · have hT' : 2^(2*k) ≤ T := by omega
    obtain ⟨hJ,hL,hkT,hHJ,hhalf,hwidth,hU⟩ := tail_parameters hk hT'
    let J := T/2^(2*k)
    let H := T-2*k
    let L := H-J
    have hcover := refined_cover (K := 32*(k+1)) (T := T) (by positivity) hHJ
    have hM : mass (band J (T+1)) ≤ 8*(k+1:ℕ) := by
      have hh := band_mass_bound hJ hU
      change mass (band J (T+1)) ≤ 4*(2*k+1:ℕ) at hh
      push_cast at hh ⊢
      linarith
    have hf := factorNeighbors_exp_bound (fun p hp => band_primes hp) hM (2^T)
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hf
    have hl := largeCover_card hL T (2^T)
    have hLr : (0:ℝ)<L := by exact_mod_cast hL
    have hWr : (0:ℝ)<(2:ℝ)^(2*k) := by positivity
    have hw : ((T+1-L:ℕ):ℝ)/(L:ℝ) ≤ 4*(k+1:ℕ)/(2:ℝ)^(2*k) := by
      apply (div_le_div_iff₀ hLr hWr).mpr
      exact_mod_cast hwidth
    have hlarge : ((largeCover L T (2^T)).card:ℝ) ≤
        32*(2:ℝ)^T*(k+1:ℕ)/(2:ℝ)^(2*k) := by
      have hh := mul_le_mul_of_nonneg_left hw (by positivity : (0:ℝ) ≤ 8*(2:ℝ)^T)
      push_cast at hl
      change ((largeCover L T (2^T)).card:ℝ) ≤ 8*(2:ℝ)^T*(T+1-L:ℕ)/(L:ℝ) at hl
      calc
        _ ≤ 8*(2:ℝ)^T*(T+1-L:ℕ)/(L:ℝ) := hl
        _ = 8*(2:ℝ)^T*(((T+1-L:ℕ):ℝ)/(L:ℝ)) := by ring
        _ ≤ 8*(2:ℝ)^T*(4*(k+1:ℕ)/(2:ℝ)^(2*k)) := hh
        _ = _ := by ring
    have hsmall : (2:ℝ)^H=(2:ℝ)^T/(2:ℝ)^(2*k) := by
      have he : H+2*k=T := Nat.sub_add_cancel hkT
      apply (eq_div_iff hWr.ne').mpr
      rw [← pow_add,he]
    change (tailCount (32*(k+1)) (2^T):ℝ) ≤ (2:ℝ)^H+
      (largeCover L T (2^T)).card+(factorNeighbors (band J (T+1)) (32*(k+1)) (2^T)).card at hcover
    rw [hsmall] at hcover
    have hkk : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
    have hc : (1:ℝ)+32*(k+1:ℕ)+2 ≤ 64*(k+1:ℕ) := by linarith
    calc
      _ ≤ (2:ℝ)^T/(2:ℝ)^(2*k)+
          32*(2:ℝ)^T*(k+1:ℕ)/(2:ℝ)^(2*k)+2*(2:ℝ)^T/(2:ℝ)^(2*k) :=
        hcover.trans (add_le_add (add_le_add le_rfl hlarge) hf)
      _ = (2:ℝ)^T/(2:ℝ)^(2*k)*(1+32*(k+1:ℕ)+2) := by ring
      _ ≤ (2:ℝ)^T/(2:ℝ)^(2*k)*(64*(k+1:ℕ)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

/-- Uniform exponential decay in the multiplicity threshold. -/
theorem uniform_exp_tail {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    (tailCount (32*(k+1)) N:ℝ)/(N:ℝ) ≤ 128*(k+1:ℕ)/(2:ℝ)^(2*k) := by
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,div_zero]
    positivity
  have hn : 0<N := Nat.pos_of_ne_zero hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hn
  let T := Nat.log 2 N+1
  have hnT : N<2^T := Nat.lt_pow_succ_log_self (by omega) N
  have hpow : (2:ℝ)^T ≤ 2*(N:ℝ) := by
    have hh := Nat.pow_log_le_self 2 hN
    have hhi : 2^T ≤ 2*N := by dsimp [T]; rw [pow_succ]; nlinarith
    exact_mod_cast hhi
  have hc : (tailCount (32*(k+1)) N:ℝ) ≤ tailCount (32*(k+1)) (2^T) := by
    exact_mod_cast tailCount_mono (32*(k+1)) hnT.le
  have hb := dyadic_exp_tail hk T
  have hs : (tailCount (32*(k+1)) N:ℝ) ≤ 128*(N:ℝ)*(k+1:ℕ)/(2:ℝ)^(2*k) := by
    calc
      _ ≤ _ := hc.trans hb
      _ ≤ 64*(2*(N:ℝ))*(k+1:ℕ)/(2:ℝ)^(2*k) := by gcongr
      _ = _ := by ring
  apply (div_le_iff₀ hNr).mpr
  exact hs.trans_eq (by ring)

end Erdos371SupercriticalExponentialTail

#print axioms Erdos371SupercriticalExponentialTail.dyadic_exp_tail
#print axioms Erdos371SupercriticalExponentialTail.uniform_exp_tail
