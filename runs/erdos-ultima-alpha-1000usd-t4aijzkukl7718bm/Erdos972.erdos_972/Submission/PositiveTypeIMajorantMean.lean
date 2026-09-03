import Submission.RemainderPositiveTypeI

/-! At fixed cutoffs, the actual positive Type-I majorant has diverging
mean. This is a limitation of using that fixed-cutoff majorant in a prime-pair
lower bound, not a statement about the original conjecture. -/
namespace Erdos972PositiveTypeIMajorantMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972DoubleVaughan Erdos972RemainderRoughSupport
open Erdos972LogarithmicCovariance Erdos972RemainderPositiveTypeI

noncomputable def positiveTypeI (U V n : ℕ) : ℝ := max (typeIPart U V n) 0

lemma positiveTypeI_nonneg (U V n : ℕ) : 0 ≤ positiveTypeI U V n := le_max_right _ _

lemma positiveTypeI_progression {U : ℕ} (hU : 1 ≤ U) (V k : ℕ) :
    positiveTypeI U V ((max U V).factorial*k+1) = Real.log ((max U V).factorial*k+1 : ℕ) := by
  have hc : ((max U V).factorial*k+1).Coprime (max U V).factorial := by
    simpa only [add_comm] using (Nat.coprime_add_mul_left_left 1 (max U V).factorial k).mpr
      (Nat.coprime_one_left _)
  rw [positiveTypeI, typeIPart_rough (by omega) hU (le_max_left U V) (le_max_right U V) hc,
    max_eq_left (Real.log_natCast_nonneg _)]

/-- A nonnegative sequence large on one arithmetic progression has an
explicit lower mean bound. No prime number theorem is used here. -/
lemma progression_log_mean_lower (f : ℕ → ℝ) {F N : ℕ} (hF : 0 < F) (hN : 2*F ≤ N)
    (hf : ∀ n, 0 ≤ f n) (hprog : ∀ k : ℕ, 1 ≤ k → Real.log k ≤ f (F*k+1)) :
    Real.log (N/(2*F):ℕ)/(4*(F:ℝ)) ≤ total N f/N := by
  let K := N/(2*F)
  have hF1 : 1 ≤ F := hF
  have hK : 1 ≤ K := Nat.div_pos hN (by positivity)
  have hNpos : 0 < N := (by positivity : 0 < 2*F).trans_le hN
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNpos
  have hKlog := Real.log_natCast_nonneg K
  have hsize : 2*F*K ≤ N := Nat.mul_div_le N (2*F)
  have hinj : Set.InjOn (fun k : ℕ => F*k+1) (Ico K (2*K) : Set ℕ) := by
    intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hF (Nat.add_right_cancel he)
  have hsub : (Ico K (2*K)).image (fun k => F*k+1) ⊆ Ioc 0 N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    obtain ⟨_, hk2⟩ := mem_Ico.mp hk
    apply mem_Ioc.mpr
    refine ⟨by omega, ?_⟩
    have hh := Nat.mul_le_mul_left F (Nat.succ_le_of_lt hk2)
    nlinarith only [hh, hF1, hsize]
  have hsum : (K:ℝ)*Real.log K ≤ total N f := by
    calc
      _ = ∑ k ∈ Ico K (2*K), Real.log K := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Ico, show 2*K-K = K by omega]
      _ ≤ ∑ k ∈ Ico K (2*K), f (F*k+1) := by
        apply sum_le_sum
        intro k hk
        have hkK := (mem_Ico.mp hk).1
        exact (Erdos972ExponentialSum.monotone_log_natCast hkK).trans (hprog k (hK.trans hkK))
      _ = ∑ n ∈ (Ico K (2*K)).image (fun k => F*k+1), f n := (sum_image hinj).symm
      _ ≤ total N f := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)
  have hupper : N ≤ 4*F*K := by
    have hh := (Nat.lt_mul_div_succ N (show 0 < 2*F by positivity)).le
    change N ≤ 2*F*(K+1) at hh
    have hk2 : K+1 ≤ 2*K := by omega
    have hm := Nat.mul_le_mul_left (2*F) hk2
    nlinarith only [hh, hm]
  have hupperR : (N:ℝ) ≤ 4*(F:ℝ)*K := by exact_mod_cast hupper
  have hmul := mul_le_mul_of_nonneg_right hupperR hKlog
  have hbase : Real.log K/(4*(F:ℝ)) ≤ (K:ℝ)*Real.log K/N := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*F) hNR).mpr
    nlinarith only [hmul]
  exact hbase.trans (div_le_div_of_nonneg_right hsum hNR.le)

/-- An actual mean-divergence result, not divergence of an upper error
budget. It holds for every fixed positive Mobius cutoff and every V. -/
theorem positiveTypeI_mean_tendsto_atTop {U : ℕ} (hU : 1 ≤ U) (V : ℕ) :
    Tendsto (fun N : ℕ => total N (positiveTypeI U V)/N) atTop atTop := by
  let F := (max U V).factorial
  have hF : 0 < F := Nat.factorial_pos _
  have hF1 : 1 ≤ F := hF
  have hdiv : Tendsto (fun N : ℕ => N/(2*F)) atTop atTop :=
    le_of_eq (map_div_atTop_eq_nat (2*F) (by positivity))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hdiv)
  have hlim : Tendsto (fun N : ℕ => Real.log (N/(2*F):ℕ)/(4*(F:ℝ))) atTop atTop := by
    have hh := hlog.const_mul_atTop (show (0:ℝ) < 1/(4*F) by positivity)
    simpa only [Function.comp_apply, one_div, div_eq_mul_inv, one_mul, mul_comm] using hh
  apply tendsto_atTop_mono' atTop _ hlim
  filter_upwards [eventually_ge_atTop (2*F)] with N hN
  apply progression_log_mean_lower (positiveTypeI U V) hF hN (positiveTypeI_nonneg U V)
  intro k hk
  rw [positiveTypeI_progression hU]
  exact Erdos972ExponentialSum.monotone_log_natCast (by
    dsimp only [F] at hF1 ⊢
    nlinarith only [Nat.mul_le_mul_right k hF1])

#print axioms positiveTypeI_progression
#print axioms positiveTypeI_mean_tendsto_atTop

end Erdos972PositiveTypeIMajorantMean
